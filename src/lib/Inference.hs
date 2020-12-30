-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Inference (inferModule) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Foldable (fold, toList)
import Data.Functor
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import Data.String (fromString)
import qualified Data.Set as S
import Data.Text.Prettyprint.Doc

import Syntax
import Interpreter (indicesNoIO)
import Embed  hiding (sub)
import Env
import Type
import PPrint
import Cat
import Util
import Control.Monad.Writer.Class (MonadWriter)

-- === type inference ===

type UInferM = ReaderT SubstEnv (ReaderT SrcCtx (EmbedT (SolverT ExceptWithOutputs)))

type SigmaType = Type  -- may     start with an implicit lambda
type RhoType   = Type  -- doesn't start with an implicit lambda
data RequiredTy a = Concrete a | Suggest a | Infer deriving (Show, Functor, Foldable, Traversable)

pattern Check :: a -> RequiredTy a
pattern Check t <-
  ((\case Concrete t -> Just t
          Suggest  t -> Just t
          Infer      -> Nothing) -> Just t)
  where Check t = Suggest t

{-# COMPLETE Infer, Check #-}

inferModule :: TopEnv -> UModule -> ExceptWithOutputs Module
inferModule scope (UModule decls) = do
  let infer = mapM_ (inferUDecl True) decls
  res <- runSolverT $ do
    res <- runEmbedT (runReaderT (runReaderT infer mempty) Nothing) scope
    logInfo TypePass $ pprint $ asModule Typed res
    return res
  return $ asModule Core res
  where asModule variant ((), (bindings, decls')) =
          let bindings' = envFilter bindings $ \(_, b) -> case b of
                            DataBoundTypeCon _   -> True
                            DataBoundDataCon _ _ -> True
                            _ -> False
          in Module variant decls' bindings'

checkSigma :: UExpr -> (Type -> RequiredTy Type) -> SigmaType -> UInferM Atom
checkSigma expr reqCon sTy = case sTy of
  Pi piTy@(Abs _ (arrow, _))
    | arrow `elem` [ImplicitArrow, ClassArrow] -> case expr of
        WithSrc _ (ULam b arrow' body) | arrow' == void arrow ->
          checkULam b body piTy
        _ -> do
          buildLam (Bind ("a":> absArgType piTy)) arrow $ \x@(Var v) ->
            checkLeaks [v] $ checkSigma expr reqCon $ snd $ applyAbs piTy x
  _ -> checkOrInferRho expr (reqCon sTy)

inferSigma :: UExpr -> UInferM Atom
inferSigma (WithSrc pos expr) = case expr of
  ULam pat ImplicitArrow body -> addSrcContext' pos $
    inferULam pat ImplicitArrow body
  _ ->
    inferRho (WithSrc pos expr)

checkRho :: UExpr -> RhoType -> UInferM Atom
checkRho expr ty = checkOrInferRho expr (Check ty)

inferRho :: UExpr -> UInferM Atom
inferRho expr = checkOrInferRho expr Infer

checkOrInferRho :: UExpr -> RequiredTy RhoType -> UInferM Atom
checkOrInferRho (WithSrc pos expr) reqTy = do
 addSrcContext' pos $ case expr of
  UVar v -> do
    ctx <- getSrcCtx
    lookupSourceVar v >>= instantiateSigma ctx >>= matchRequirement
  ULam (p, ann) ImplicitArrow body -> do
    argTy <- checkAnn ann
    x <- freshType argTy
    withBindPat p x $ checkOrInferRho body reqTy
  ULam b arr body -> do
    let infer = inferULam b (fmap (const Pure) arr) body
    case reqTy of
      Check (Pi piTy@(Abs _ (arrReq, _))) -> do
        checkArrow arrReq arr
        checkULam b body piTy
      Check _ -> infer >>= matchRequirement
      Infer   -> infer
  UFor dir b body -> do
    let infer = do
          allowedEff <- getAllowedEffects
          lam <- inferULam b (PlainArrow allowedEff) body
          emitZonked $ Hof $ For (RegularFor dir) lam
    case reqTy of
      Check (Pi (Abs n (arr, a))) -> do
        unless (arr == TabArrow) $
          throw TypeErr $ "Not an table arrow type: " ++ pprint arr
        allowedEff <- getAllowedEffects
        lam <- checkULam b body $ Abs n (PlainArrow allowedEff, a)
        emitZonked $ Hof $ For (RegularFor dir) lam
      Check _ -> infer >>= matchRequirement
      Infer   -> infer
  UApp arr f x@(WithSrc xPos _) -> do
    fVal <- inferRho f
    -- NB: We never infer dependent function types, but we accept them, provided they
    --     come with annotations. So, unless we already know that the function is
    --     dependent here (i.e. the type of the zonk comes as a dependent Pi type),
    --     then nothing in the remainder of the program can convince us that the type
    --     is dependent. Also, the Pi binder is never considered to be in scope for
    --     inference variables, so they cannot get unified with it. Hence, this zonk
    --     is safe and doesn't make the type checking depend on the program order.
    infTy <- getType <$> zonk fVal
    piTy  <- addSrcContext' (srcPos f) $ fromPiType True arr infTy
    (xVal, embedEnv@(_, xDecls)) <- embedScoped $ checkSigma x Suggest (absArgType piTy)
    (xVal', arr') <- case piTy of
      Abs b rhs@(arr', _) -> case b `isin` freeVars rhs of
        False -> embedExtend embedEnv $> (xVal, arr')
        True  -> do
          xValMaybeRed <- flip typeReduceBlock (Block xDecls (Atom xVal)) <$> getScope
          case xValMaybeRed of
            Just xValRed -> return (xValRed, fst $ applyAbs piTy xValRed)
            Nothing      -> addSrcContext' xPos $ do
              throw TypeErr $ "Dependent functions can only be applied to fully " ++
                              "evaluated expressions. Bind the argument to a name " ++
                              "before you apply the function."
    addEffects $ arrowEff arr'
    appVal <- emitZonked $ App fVal xVal'
    ctx <- getSrcCtx
    instantiateSigma ctx appVal >>= matchRequirement
  UPi (pat, kind) arr ty -> do
    -- TODO: make sure there's no effect if it's an implicit or table arrow
    -- TODO: check leaks
    kind' <- checkUType kind
    piTy <- case pat of
      Just pat' -> withNameHint ("pat" :: Name) $ buildPi b $ \x ->
        withBindPat pat' x $ (,) <$> mapM checkUEff arr <*> checkUType ty
        where b = case pat' of
                    -- Note: The binder name becomes part of the type, so we
                    -- need to keep the same name used in the pattern.
                    WithSrc _ (UPatBinder (Bind (v:>()))) -> Bind (v:>kind')
                    _ -> Ignore kind'
      Nothing -> buildPi (Ignore kind') $ const $
        (,) <$> mapM checkUEff arr <*> checkUType ty
    matchRequirement piTy
  UDecl decl body -> do
    env <- inferUDecl False decl
    extendR env $ checkOrInferRho body reqTy
  UCase scrut alts -> do
    scrut' <- inferRho scrut
    let scrutTy = getType scrut'
    reqTy' <- case reqTy of
      Infer -> freshType TyKind
      Check req -> return req
    alts' <- mapM (checkCaseAlt reqTy' scrutTy) alts
    scrutTy' <- zonk scrutTy
    scrut'' <- zonk scrut'
    case scrutTy' of
      TypeCon def params -> do
        let conDefs = applyDataDefParams def params
        altsSorted <- forM (enumerate conDefs) $ \(i, DataConDef _ bs) -> do
          case lookup (ConAlt i) alts' of
            Nothing  -> return $ Abs (fmap (Ignore . binderType) bs) $
                                  Block Empty $ Op $ ThrowError reqTy'
            Just alt -> return alt
        emit $ Case scrut'' altsSorted reqTy'
      VariantTy (Ext types@(LabeledItems tyItems) tailName) -> do
        let unhandledCase :: Type -> Alt
            unhandledCase ty = Abs (toNest [Ignore ty]) $
                              Block Empty $ Op $ ThrowError reqTy'
        let buildMonomorphicCase :: LabeledItems Type -> Atom -> UInferM Atom
            buildMonomorphicCase monoTypes monoScrut = do
              altsSorted <- forM (toList (withLabels monoTypes)) $
                \(l, i, ty) -> case lookup (VariantAlt l i) alts' of
                    Nothing  -> return $ unhandledCase ty
                    Just alt -> return alt
              emit $ Case monoScrut altsSorted reqTy'
        let isVariantTailAlt (VariantTailAlt _) = True
            isVariantTailAlt _ = False
        case filter (isVariantTailAlt . fst) alts' of
          [] -> case tailName of
            Nothing ->
              -- We already know the type exactly, so just emit a case.
              buildMonomorphicCase types scrut''
            Just _ -> do
              -- Split off the types we don't know about, mapping them to a
              -- runtime error.
              split <- emit $ Op $ VariantSplit types scrut''
              VariantTy (NoExt (Unlabeled [leftTy, rightTy])) <-
                return $ getType split
              leftCase <- buildNAbs (toNest [Ignore leftTy])
                                    (\[v] -> buildMonomorphicCase types v)
              emit $ Case split [leftCase, unhandledCase rightTy] reqTy'
          [(VariantTailAlt (LabeledItems skippedItems), tailAlt)] -> do
            -- Split off the types skipped by the tail pattern.
            let splitLeft fvs ltys = NE.fromList $ NE.take (length ltys) fvs
                left = M.intersectionWith splitLeft tyItems skippedItems
            -- Make sure all of the alternatives are exclusive with the tail
            -- pattern (could technically allow overlap but this is simpler).
            let overlapErr = throw TypeErr
                  "Variant explicit alternatives overlap with tail pattern."
            let checkAltAgainstTail :: CaseAltIndex -> UInferM ()
                checkAltAgainstTail (VariantAlt label i) =
                  case M.lookup label left of
                    Just tys -> if i <= length tys
                                then return ()
                                else overlapErr
                    Nothing -> overlapErr
                checkAltAgainstTail _ = return ()
            mapM_ (checkAltAgainstTail . fst) alts'
            -- Split based on the tail pattern's skipped types.
            split <- emit $ Op $ VariantSplit (LabeledItems left) scrut''
            let leftTy = VariantTy $ NoExt $ LabeledItems left
            leftCase <-
              buildNAbs (toNest [Ignore leftTy])
                (\[v] -> buildMonomorphicCase (LabeledItems left) v)
            emit $ Case split [leftCase, tailAlt] reqTy'
          _ -> throw TypeErr "Can't specify more than one variant tail pattern."
      _ -> fail $ "Unexpected case expression type: " <> pprint scrutTy'
  UTabCon xs -> inferTabCon xs reqTy >>= matchRequirement
  UIndexRange low high -> do
    n <- freshType TyKind
    low'  <- mapM (flip checkRho n) low
    high' <- mapM (flip checkRho n) high
    matchRequirement $ TC $ IndexRange n low' high'
  UHole -> case reqTy of
    Infer -> throw MiscErr "Can't infer type of hole"
    Check ty -> freshType ty
  UTypeAnn val ty -> do
    ty' <- zonk =<< checkUType ty
    let reqCon = if null (toList $ freeVars ty') then Concrete else Suggest
    val' <- checkSigma val reqCon ty'
    matchRequirement val'
  UPrimExpr prim -> do
    prim' <- forM prim $ \e -> do
      e' <- inferRho e
      scope <- getScope
      return $ typeReduceAtom scope e'
    val <- case prim' of
      TCExpr  e -> return $ TC e
      ConExpr e -> return $ Con e
      OpExpr  e -> emitZonked $ Op e
      HofExpr e -> emitZonked $ Hof e
    matchRequirement val
  URecord (Ext items Nothing) -> do
    items' <- mapM inferRho items
    matchRequirement $ Record items'
  URecord (Ext items (Just ext)) -> do
    items' <- mapM inferRho items
    restTy <- freshInferenceName LabeledRowKind
    ext' <- zonk =<< (checkRho ext $ RecordTy $ Ext NoLabeledItems $ Just restTy)
    matchRequirement =<< emit (Op $ RecordCons items' ext')
  UVariant labels@(LabeledItems lmap) label value -> do
    value' <- inferRho value
    prevTys <- mapM (const $ freshType TyKind) labels
    rest <- freshInferenceName LabeledRowKind
    let items = prevTys <> labeledSingleton label (getType value')
    let extItems = Ext items $ Just rest
    let i = case M.lookup label lmap of
              Just prev -> length prev
              Nothing -> 0
    matchRequirement $ Variant extItems label i value'
  URecordTy row -> matchRequirement =<< RecordTy <$> checkExtLabeledRow row
  UVariantTy row -> matchRequirement =<< VariantTy <$> checkExtLabeledRow row
  UVariantLift labels value -> do
    row <- freshInferenceName LabeledRowKind
    value' <- zonk =<< (checkRho value $ VariantTy $ Ext NoLabeledItems $ Just row)
    prev <- mapM (\() -> freshType TyKind) labels
    matchRequirement =<< emit (Op $ VariantLift prev value')
  UIntLit  x  -> matchRequirement $ Con $ Lit  $ Int32Lit $ fromIntegral x
  UFloatLit x -> matchRequirement $ Con $ Lit  $ Float32Lit $ realToFrac x
  -- TODO: Make sure that this conversion is not lossy!
  where
    matchRequirement :: Atom -> UInferM Atom
    matchRequirement x = return x <*
      case reqTy of
        Infer -> return ()
        Check req -> constrainEq req (getType x)

lookupSourceVar :: UVar -> UInferM Atom
lookupSourceVar v = do
  substEnv <- ask
  case envLookup substEnv v of
    Just x -> return x
    Nothing -> do
      scope <- getScope
      let v' = asGlobal $ varName v
      case envLookup scope v' of
        Just (_, DataBoundTypeCon def    ) -> return $ TypeCon def []
        Just (_, DataBoundDataCon def con) -> return $ DataCon def [] con []
        Just (ty, _) -> return $ Var $ v':>ty
        Nothing -> throw UnboundVarErr $ pprint $ asGlobal $ varName v

unpackTopPat :: LetAnn -> UPat -> Expr -> UInferM ()
unpackTopPat letAnn pat expr = do
  atom <- emit expr
  bindings <- bindPat pat atom
  void $ flip traverseNames bindings $ \name val -> do
    let name' = asGlobal name
    scope <- getScope
    when (name' `isin` scope) $ throw RepeatedVarErr $ pprint $ name'
    emitTo name' letAnn $ Atom val

inferUDecl :: Bool -> UDecl -> UInferM SubstEnv
inferUDecl topLevel (ULet letAnn (p, ann) rhs) = do
  -- We don't display global names in any visually distinct way from local names
  -- so avoid giving the name hint for top-level declarations. Otherwise we might
  -- end up with x = x decls in the module (with left x being global and right being local).
  let nameHint = if topLevel then liftM id else withPatHint p
  val <- nameHint $ case ann of
    Nothing -> inferSigma rhs
    Just ty -> do
      ty' <- zonk =<< checkUType ty
      let reqCon = if null (toList $ freeVars ty') then Concrete else Suggest
      checkSigma rhs reqCon ty'
  expr <- zonk $ Atom val
  if topLevel
    then unpackTopPat letAnn p expr $> mempty
    else bindPat p val
inferUDecl True (UData tc dcs) = do
  (tc', paramBs) <- inferUConDef tc
  scope <- getScope
  when (tc' `isin` scope) $ throw RepeatedVarErr $ pprint $ getName tc'
  let paramVars = map (\(Bind v) -> v) $ toList paramBs  -- TODO: refresh things properly
  (dcs', _) <- embedScoped $
    extendR (newEnv paramBs (map Var paramVars)) $ do
      extendScope (foldMap boundVars paramBs)
      mapM inferUConDef dcs
  let dataDef = DataDef tc' paramBs $ map (uncurry DataConDef) dcs'
  let tyConTy = getType $ TypeCon dataDef []
  extendScope $ tc' @> (tyConTy, DataBoundTypeCon dataDef)
  forM_ (zip [0..] dcs') $ \(i, (dc,_)) -> do
    -- Retrieving scope at every step to avoid duplicate constructor names
    scope' <- getScope
    when (dc `isin` scope') $ throw RepeatedVarErr $ pprint $ getName dc
    let ty = getType $ DataCon dataDef [] i []
    extendScope $ dc @> (ty, DataBoundDataCon dataDef i)
  return mempty
inferUDecl False (UData _ _) = error "data definitions should be top-level"

inferUConDef :: UConDef -> UInferM (Name, Nest Binder)
inferUConDef (UConDef v bs) = do
  (bs', _) <- embedScoped $ checkNestedBinders bs
  return (asGlobal  v, bs')

checkNestedBinders :: Nest UAnnBinder -> UInferM (Nest Binder)
checkNestedBinders Empty = return Empty
checkNestedBinders (Nest b bs) = do
  b' <- mapM checkUType b
  extendScope (boundVars b')
  let env = case b' of Bind v   -> b' @> Var v
                       Ignore _ -> mempty
  bs' <- extendR env $ checkNestedBinders bs
  return $ Nest b' bs'

inferULam :: UPatAnn -> Arrow -> UExpr -> UInferM Atom
inferULam (p, ann) arr body = do
  argTy <- checkAnn ann
  -- TODO: worry about binder appearing in arrow?
  buildLam (Bind $ patNameHint p :> argTy) arr
    $ \x@(Var v) -> checkLeaks [v] $ withBindPat p x $ inferSigma body

checkULam :: UPatAnn -> UExpr -> PiType -> UInferM Atom
checkULam (p, ann) body piTy = do
  let argTy = absArgType piTy
  checkAnn ann >>= constrainEq argTy
  buildDepEffLam (Bind $ patNameHint p :> argTy)
    ( \x -> return $ fst $ applyAbs piTy x)
    $ \x@(Var v) -> checkLeaks [v] $ withBindPat p x $
                      checkSigma body Suggest $ snd $ applyAbs piTy x

checkUEff :: EffectRow -> UInferM EffectRow
checkUEff (EffectRow effs t) = do
   effs' <- liftM S.fromList $ forM (toList effs) $ \(effName, region) -> do
     (Var (v:>TyKind)) <- lookupSourceVar (region:>())
     return (effName, v)
   t'    <- forM t $ \tv -> lookupVarName EffKind tv
   return $ EffectRow effs' t'
   where
     lookupVarName :: Type -> Name -> UInferM Name
     lookupVarName ty v = do
       -- TODO: more graceful errors on error
       Var (v':>ty') <- asks (!(v:>()))
       constrainEq ty ty'
       return v'

data CaseAltIndex = ConAlt Int
                  | VariantAlt Label Int
                  | VariantTailAlt (LabeledItems ())
  deriving (Eq, Show)

checkCaseAlt :: RhoType -> Type -> UAlt -> UInferM (CaseAltIndex, Alt)
checkCaseAlt reqTy scrutineeTy (UAlt pat body) = do
  (conIdx, patTys) <- checkCasePat pat scrutineeTy
  let (subPats, subPatTys) = unzip patTys
  let bs = zipWith (\p ty -> Bind $ patNameHint p :> ty) subPats subPatTys
  alt <- buildNAbs (toNest bs) $ \xs ->
           withBindPats (zip subPats xs) $ checkRho body reqTy
  return (conIdx, alt)

lookupDataCon :: Name -> UInferM (DataDef, Int)
lookupDataCon conName = do
  let conName' = asGlobal conName
  scope <- getScope
  case envLookup scope (conName':>()) of
    Just (_, DataBoundDataCon def con) -> return (def, con)
    Just _  -> throw TypeErr $ "Not a data constructor: " ++ pprint conName'
    Nothing -> throw UnboundVarErr $ pprint conName'

checkCasePat :: UPat -> Type -> UInferM (CaseAltIndex, [(UPat, Type)])
checkCasePat (WithSrc pos pat) scrutineeTy = addSrcContext' pos $ case pat of
  UPatCon conName ps -> do
    (def@(DataDef _ paramBs cons), con) <- lookupDataCon conName
    let (DataConDef _ argBs) = cons !! con
    when (length argBs /= length ps) $ throw TypeErr $
     "Unexpected number of pattern binders. Expected " ++ show (length argBs)
                                            ++ " got " ++ show (length ps)
    params <- mapM (freshType . binderType) $ toList paramBs
    let argTys = applyNaryAbs (Abs paramBs $ map binderType $ toList argBs) params
    constrainEq scrutineeTy (TypeCon def params)
    return (ConAlt con, zip (toList ps) argTys)
  UPatVariant labels@(LabeledItems lmap) label subpat -> do
    subty <- freshType TyKind
    prevTys <- mapM (const $ freshType TyKind) labels
    Var (rest:>_) <- freshType LabeledRowKind
    let patTypes = prevTys <> labeledSingleton label subty
    let extPatTypes = Ext patTypes $ Just rest
    constrainEq scrutineeTy $ VariantTy extPatTypes
    let i = case M.lookup label lmap of
              Just prev -> length prev
              Nothing -> 0
    return (VariantAlt label i, [(subpat, subty)])
  UPatVariantLift labels subpat -> do
    prevTys <- mapM (const $ freshType TyKind) labels
    Var (rest:>_) <- freshType LabeledRowKind
    let extPatTypes = Ext prevTys $ Just rest
    constrainEq scrutineeTy $ VariantTy extPatTypes
    let subty = VariantTy $ Ext NoLabeledItems $ Just rest
    return (VariantTailAlt labels, [(subpat, subty)])
  _ -> throw TypeErr $ "Case patterns must start with a data constructor or variant pattern"

withBindPats :: [(UPat, Atom)] -> UInferM a -> UInferM a
withBindPats pats body = foldr (uncurry withBindPat) body pats

withBindPat :: UPat -> Atom -> UInferM a -> UInferM a
withBindPat pat val m = do
  env <- bindPat pat val
  extendR env m

bindPat :: UPat -> Atom -> UInferM SubstEnv
bindPat pat val = evalCatT $ bindPat' pat val

-- CatT wrapper is used to prevent duplicate bindings within the same pattern,
-- e.g. (a, a) = (1, 2) should throw RepeatedVarErr
bindPat' :: UPat -> Atom -> CatT (Env ()) UInferM SubstEnv
bindPat' (WithSrc pos pat) val = addSrcContext pos $ case pat of
  UPatBinder b -> do
    usedVars <- look
    when (b `isin` usedVars) $ throw RepeatedVarErr $ pprint $ getName b
    extend (b @> ())
    return (b @> val)
  UPatUnit -> do
    lift $ constrainEq UnitTy (getType val)
    return mempty
  UPatPair p1 p2 -> do
    _    <- lift $ fromPairType (getType val)
    val' <- lift $ zonk val  -- ensure it has a pair type before unpacking
    x1   <- lift $ getFst val'
    x2   <- lift $ getSnd val'
    env1 <- bindPat' p1 x1
    env2 <- bindPat' p2 x2
    return $ env1 <> env2
  UPatCon conName ps -> do
    (def@(DataDef _ paramBs cons), con) <- lift $ lookupDataCon conName
    when (length cons /= 1) $ throw TypeErr $
      "sum type constructor in can't-fail pattern"
    let (DataConDef _ argBs) = cons !! con
    when (length argBs /= length ps) $ throw TypeErr $
      "Unexpected number of pattern binders. Expected " ++ show (length argBs)
                                             ++ " got " ++ show (length ps)
    params <- lift $ mapM (freshType . binderType) $ toList paramBs
    lift $ constrainEq (TypeCon def params) (getType val)
    xs <- lift $ zonk (Atom val) >>= emitUnpack
    fold <$> zipWithM bindPat' (toList ps) xs
  UPatRecord (Ext pats Nothing) -> do
    expectedTypes <- lift $ mapM (const $ freshType TyKind) pats
    lift $ constrainEq (RecordTy (NoExt expectedTypes)) (getType val)
    xs <- lift $ zonk (Atom val) >>= emitUnpack
    fold <$> zipWithM bindPat' (toList pats) xs
  UPatRecord (Ext pats (Just tailPat)) -> do
    wantedTypes <- lift $ mapM (const $ freshType TyKind) pats
    restType <- lift $ freshInferenceName LabeledRowKind
    let vty = getType val
    lift $ constrainEq (RecordTy $ Ext wantedTypes $ Just restType) vty
    -- Split the record.
    wantedTypes' <- lift $ zonk wantedTypes
    val' <- lift $ zonk val
    split <- lift $ emit $ Op $ RecordSplit wantedTypes' val'
    [left, right] <- lift $ getUnpacked split
    leftVals <- lift $ getUnpacked left
    env1 <- fold <$> zipWithM bindPat' (toList pats) leftVals
    env2 <- bindPat' tailPat right
    return $ env1 <> env2
  UPatVariant _ _ _ -> throw TypeErr "Variant not allowed in can't-fail pattern"
  UPatVariantLift _ _ -> throw TypeErr "Variant not allowed in can't-fail pattern"
  UPatTable ps -> do
    elemTy <- lift $ freshType TyKind
    let idxTy = FixedIntRange 0 (fromIntegral $ length ps)
    lift $ constrainEq (getType val) (idxTy ==> elemTy)
    let idxs = indicesNoIO idxTy
    unless (length idxs == length ps) $
      throw TypeErr $ "Incorrect length of table pattern: table index set has "
                      <> pprint (length idxs) <> " elements but there are "
                      <> pprint (length ps) <> " patterns."
    flip foldMapM (zip ps idxs) $ \(p, i) -> do
      v <- lift $ emitZonked $ App val i
      bindPat' p v

-- TODO (BUG!): this should just be a hint but something goes wrong if we don't have it
patNameHint :: UPat -> Name
patNameHint (WithSrc _ (UPatBinder (Bind (v:>())))) = v
patNameHint _ = "pat"

withPatHint :: UPat -> UInferM a -> UInferM a
withPatHint p m = withNameHint (patNameHint p) m

checkAnn :: Maybe UType -> UInferM Type
checkAnn ann = case ann of
  Just ty -> checkUType ty
  Nothing -> freshType TyKind

checkUType :: UType -> UInferM Type
checkUType ty = do
  reduced <- typeReduceScoped $ withEffects Pure $ checkRho ty TyKind
  case reduced of
    Just ty' -> return $ ty'
    Nothing  -> throw TypeErr $ "Can't reduce type expression: " ++ pprint ty

checkArrow :: Arrow -> UArrow -> UInferM ()
checkArrow ahReq ahOff = case (ahReq, ahOff) of
  (PlainArrow _, PlainArrow ()) -> return ()
  (LinArrow    , PlainArrow ()) -> return ()
  (LinArrow    , LinArrow     ) -> return ()
  (TabArrow  , TabArrow  ) -> return ()
  (ClassArrow, ClassArrow) -> return ()
  _ -> throw TypeErr $  " Wrong arrow type:" ++
                       "\nExpected: " ++ pprint ahReq ++
                       "\nActual:   " ++ pprint (fmap (const Pure) ahOff)

checkExtLabeledRow :: ExtLabeledItems UExpr UExpr -> UInferM (ExtLabeledItems Type Name)
checkExtLabeledRow (Ext types Nothing) = do
  types' <- mapM checkUType types
  return $ Ext types' Nothing
checkExtLabeledRow (Ext types (Just ext)) = do
  types' <- mapM checkUType types
  -- Only variables can have kind LabeledRowKind at the moment.
  Var (ext':>_) <- checkRho ext LabeledRowKind
  return $ Ext types' $ Just ext'

inferTabCon :: [UExpr] -> RequiredTy RhoType -> UInferM Atom
inferTabCon xs reqTy = do
  (tabTy, xs') <- case reqTy of
    Concrete tabTy@(TabTyAbs a) -> do
      let idx = indicesNoIO $ absArgType a
      -- TODO: Check length!!
      unless (length idx == length xs) $
        throw TypeErr "Table type doesn't match annotation"
      xs' <- mapM (\(x, i) -> checkOrInferRho x $ Concrete $ snd $ applyAbs a i) $ zip xs idx
      return (tabTy, xs')
    _ -> do
      elemTy <- case xs of
        []    -> freshType TyKind
        (x:_) -> getType <$> inferRho x
      let tabTy = (FixedIntRange 0 (fromIntegral $ length xs)) ==> elemTy
      case reqTy of
        Suggest sTy -> addContext context $ constrainEq sTy tabTy
          where context = "If attempting to construct a fixed-size table not " <>
                          "indexed by 'Fin n' for some n, this error may " <>
                          "indicate there was not enough information to infer " <>
                          "a concrete index set; try adding an explicit " <>
                          "annotation."
        Infer       -> return ()
        _           -> error "Missing case"
      xs' <- mapM (flip checkRho elemTy) xs
      return (tabTy, xs')
  emitZonked $ Op $ TabCon tabTy xs'

-- Bool flag is just to tweak the reported error message
fromPiType :: Bool -> UArrow -> Type -> UInferM PiType
fromPiType _ _ (Pi piTy) = return piTy -- TODO: check arrow
fromPiType expectPi arr ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  let piTy = Abs (Ignore a) (fmap (const Pure) arr, b)
  if expectPi then  constrainEq (Pi piTy) ty
              else  constrainEq ty (Pi piTy)
  return piTy

fromPairType :: Type -> UInferM (Type, Type)
fromPairType (PairTy t1 t2) = return (t1, t2)
fromPairType ty = do
  a <- freshType TyKind
  b <- freshType TyKind
  constrainEq (PairTy a b) ty
  return (a, b)

addEffects :: EffectRow -> UInferM ()
addEffects eff = do
  allowed <- checkAllowedUnconditionally eff
  unless allowed $ do
    allowedEffects <- getAllowedEffects
    eff' <- openEffectRow eff
    constrainEq (Eff allowedEffects) (Eff eff')

checkAllowedUnconditionally :: EffectRow -> UInferM Bool
checkAllowedUnconditionally Pure = return True
checkAllowedUnconditionally eff = do
  eff' <- zonk eff
  effAllowed <- getAllowedEffects >>= zonk
  return $ case checkExtends effAllowed eff' of
    Left _   -> False
    Right () -> True

openEffectRow :: EffectRow -> UInferM EffectRow
openEffectRow (EffectRow effs Nothing) = extendEffRow effs <$> freshEff
openEffectRow effRow = return effRow

addSrcContext' :: SrcCtx -> UInferM a -> UInferM a
addSrcContext' pos m = do
  env <- ask
  addSrcContext pos $ lift $
    local (const pos) $ runReaderT m env

getSrcCtx :: UInferM SrcCtx
getSrcCtx = lift ask

-- === constraint solver ===

data SolverEnv = SolverEnv
  { solverVars :: Env Kind        -- All variables we need to solve for.
  , wantedDictVars :: Env (Scope, SrcCtx, Type)    -- Wanted typeclass instances. A variable that
                                  -- appears as v@>ty in `wantedDictVars` should
                                  -- resolve to a lambda of type `Unit -> ty`.
  , solverSub  :: Env Type        -- Substitutions for solved vars.
  }
type SolverT m = CatT SolverEnv m

instance Semigroup SolverEnv where
  -- TODO: as an optimization, don't do the subst when sub2 is empty
  -- TODO: make concatenation more efficient by maintaining a reverse-lookup map
  SolverEnv scope1 dv1 sub1 <> SolverEnv scope2 dv2 sub2 =
    SolverEnv (scope1 <> scope2) (dv1 <> dv2) (sub1' <> sub2)
    where sub1' = fmap (scopelessSubst sub2) sub1

instance Monoid SolverEnv where
  mempty = SolverEnv mempty mempty mempty
  mappend = (<>)

runSolverT :: (MonadError Err m, MonadWriter [Output] m, Subst a, Pretty a)
           => CatT SolverEnv m a -> m a
runSolverT m = fmap fst $ flip runCatT mempty $ do
  ans <- m
  withZonkedContext ans $ do
    -- Resolve all remaining constraints.
    resolveConstraints
    applyDefaults
    -- Make sure there are no ambiguous type variables.
    ans' <- zonk ans
    vs <- looks $ envNames . unsolved
    throwIf (not (null vs)) TypeErr $ "Ambiguous type variables: " ++ pprint vs
    return ans'

withZonkedContext :: (MonadError Err m, Subst a, Pretty a, MonadCat SolverEnv m)
                  => a -> m b -> m b
withZonkedContext ans m = catchError m $ \(Err e p s) -> do
  ans' <- zonk ans
  throwError $ Err e p (s ++ "\n\nWhile solving:\n" ++ pprint ans')

-- Resolve any deferred typeclass constraints.
resolveConstraints :: ( MonadError Err m, MonadCat SolverEnv m
                      , MonadWriter [Output] m) => m ()
resolveConstraints = go 0 where
  go i = do
    dicts <- looks unsolvedDicts
    if null dicts then return () else do
      -- If we took too long, throw an error.
      when (i >= maxIters) throwMaxItersError
      -- Try to solve each dictionary.
      solved <- forM (envPairs dicts) $ \(v, (scope, ctx, ty)) -> do
        soln <- trySynth scope ctx ty
        case soln of
          Just dict -> bindQ (v:>()) dict >> return True
          Nothing -> return False
      -- If we made no progress, throw an error.
      unless (or solved) throwResolutionError
      -- Try solving again.
      go (i + 1)
  throwResolutionError = do
    env <- look
    zonkedDicts <- mapM (\(_, _, ty) -> zonk ty) $ unsolvedDicts env
    throw TypeErr  $
      "Got stuck solving typeclass dictionaries:\n" ++ pprint zonkedDicts
      ++ "\n\nUnsolveable type variables:\n"
      ++ pprint (unsolved env `envDiff` zonkedDicts)
  throwMaxItersError = do
    env <- look
    zonkedDicts <- mapM (\(_, _, ty) -> zonk ty) $ unsolvedDicts env
    throw TypeErr  $
      "Maximum iterations (" ++ show maxIters
      ++ ") reached solving for instance dictionaries:\n" ++ pprint zonkedDicts
      ++ "\n\nUnsolveable type variables:\n"
      ++ pprint (unsolved env `envDiff` zonkedDicts)
  maxIters :: Int
  maxIters = 1000

-- Apply default values for unknown type variables.
applyDefaults :: MonadCat SolverEnv m => m ()
applyDefaults = do
  vs <- looks unsolved
  forM_ (envPairs vs) $ \(v, k) -> case k of
    EffKind -> addSub v $ Eff Pure
    _ -> return ()
  where addSub v ty = extend $ mempty{solverSub=v@>ty}

-- Adding new solver variables

freshInferenceName :: (MonadError Err m, MonadCat SolverEnv m) => Kind -> m Name
freshInferenceName k = do
  env <- look
  let v = genFresh (rawName InferenceName "?") $ solverVars env
  extend $ mempty {solverVars=v@>k}
  return v

freshType ::  (MonadError Err m, MonadCat SolverEnv m) => Kind -> m Type
freshType EffKind = Eff <$> freshEff
freshType k = Var . (:>k) <$> freshInferenceName k

freshEff :: (MonadError Err m, MonadCat SolverEnv m) => m EffectRow
freshEff = EffectRow mempty . Just <$> freshInferenceName EffKind

makeClassDict :: (MonadError Err m, MonadCat SolverEnv m, MonadEmbed m)
              => SrcCtx -> Type -> m Atom
makeClassDict ctx ty = do
  scope <- getScope
  -- Synthesis results in a "thunk" that we have to call, since we might need
  -- to run computation to emit the dictionary.
  -- During simplification (and also during type-level reduction), once we
  -- have solved the instance, this App will be beta-reduced away. But until
  -- we solve it, the App allows us to safely refer to the result of the
  -- unknown computation.
  v <- freshInferenceName thunkTy
  -- Remember what type we are solving for, so we can synthesize it later.
  extend $ mempty {wantedDictVars=v@>(scope, ctx, ty)}
  emit $ App (Var $ v:>thunkTy) UnitVal
  where thunkTy = Pi $ makeAbs (Ignore UnitTy) (PureArrow, ty)

bindQ :: (MonadCat SolverEnv m, MonadError Err m, Pretty v) => VarP v -> Type -> m ()
bindQ v t | v `occursIn` t = throw TypeErr $ "Occurs check failure: " ++ pprint (v, t)
          | hasSkolems t = throw TypeErr "Can't unify with skolem vars"
          | otherwise = extend $ mempty { solverSub = v@>t }

-- === typeclass dictionary synthesizer ===

-- Synthesis produces a name identifying the instance, a "thunk" atom that
-- computes the dictionary, and possible additional constraints to solve for.
type SynthOutcome = [(Name, Atom, SolverEnv)]

-- If an instance might apply after solving for some currently-unknown type
-- variables, we should keep trying.
data SynthConfidence = SynthFoundAll | SynthCouldFindMore

type SynthAttempt = (SynthOutcome, SynthConfidence)

instance Semigroup SynthConfidence where
  SynthFoundAll <> SynthFoundAll = SynthFoundAll
  _ <> _ = SynthCouldFindMore

instance Monoid SynthConfidence where
  mempty = SynthFoundAll

-- Try to synthesize an instance dictionary. If the results depend on unknown
-- inference variables, this may return Nothing.
trySynth :: (MonadCat SolverEnv m, MonadError Err m, MonadWriter [Output] m)
         => Scope -> SrcCtx -> Type -> m (Maybe Atom)
trySynth scope ctx ty = addSrcContext ctx $ do
  scope' <- zonk scope
  ty' <- zonk ty
  -- Run in a local scope.
  (result, (_, decls)) <- runEmbedT (synthInScope ctx ty') scope'
  throwIf (not $ null decls) CompilerErr "Unexpected decls in synthWithOptions"
  case result of
    (solutions@(_:_:_), confidence) -> throw TypeErr $
      "Multiple candidate class dictionaries for: " ++ pprint ty'
           ++ "\n" ++ pprint dictNames ++ andPossiblyOthers
      where
        dictNames = map (\(n, _, _) -> n) solutions
        andPossiblyOthers = case confidence of
          SynthFoundAll -> ""
          SynthCouldFindMore -> "\n(and possibly others after solving for "
                                <> "remaining type variables)"
    (_, SynthCouldFindMore) -> return Nothing
    ([(_, dict, env)], SynthFoundAll) ->
      extend env >> return (Just dict)
    ([], SynthFoundAll) -> throw TypeErr $
      "Couldn't synthesize a class dictionary for: " ++ pprint ty'

-- Try to find a dictionary, trying lambda-bound dictionaries before global
-- instances.
synthInScope :: ( MonadCat SolverEnv m, MonadEmbed m, MonadError Err m
                , MonadWriter [Output] m)
             => SrcCtx -> Type -> m SynthAttempt
synthInScope ctx ty = do
  scope <- getScope
  -- first, try to find a lam-bound class dict we can use.
  let lamBoundAndSuperclassDicts = do
        v <- getLamBoundDicts scope
        dict <- useDictOrSuperclass ctx scope (Var v)
        return (varName v, dict)
  lamBoundAttempt <- synthWithOptions ctx ty lamBoundAndSuperclassDicts
  case lamBoundAttempt of
    ([], SynthFoundAll) -> do
      -- if we are sure we can't find it as a lam-bound class, try to find
      -- a standalone instance.
      let instanceDicts = getInstances scope
      synthWithOptions ctx ty $
        (\v -> (varName v, return $ Var v)) <$>instanceDicts
    found -> return found

-- TODO: this doesn't de-dup, so we'll get multiple results if we have a
-- diamond-shaped hierarchy.
useDictOrSuperclass :: (MonadCat SolverEnv m, MonadEmbed m, MonadError Err m)
           => SrcCtx -> Scope -> Atom -> [m Atom]
useDictOrSuperclass ctx scope dict = return dict : do
  (f, LetBound SuperclassLet _) <- getBindings scope
  return $ tryApply ctx (Var f) dict

tryApply :: (MonadCat SolverEnv m, MonadEmbed m, MonadError Err m)
         => SrcCtx -> Atom -> Atom -> m Atom
tryApply ctx f x = do
  f' <- instantiateSigma ctx f
  b <- case getType f' of
    Pi (Abs b _) -> return b
    _ -> throw CompilerErr "expected pi type in tryApply"
  constrainEq (binderType b) (getType x)
  emitZonked $ App f' x

getBindings :: Scope -> [(Var, BinderInfo)]
getBindings scope = do
  (v, (ty, bindingInfo)) <- envPairs scope
  return (v:>ty, bindingInfo)

getInstances :: Scope -> [Var]
getInstances scope = do
  (v, LetBound InstanceLet _) <- getBindings scope
  return v

getLamBoundDicts :: Scope -> [Var]
getLamBoundDicts scope = do
  (v, LamBound ClassArrow) <- getBindings scope
  return v

synthWithOptions :: ( MonadCat SolverEnv m, MonadEmbed m, MonadError Err m
                    , MonadWriter [Output] m)
                 => SrcCtx -> Type -> [(Name, m Atom)] -> m SynthAttempt
synthWithOptions ctx ty = foldMapM (synthOption ctx ty)

synthOption :: ( MonadCat SolverEnv m, MonadEmbed m, MonadError Err m
               , MonadWriter [Output] m)
               => SrcCtx -> Type -> (Name, m Atom) -> m SynthAttempt
synthOption ctx ty (name, dict) = do
  -- Locally unify and construct the dictionary, ignoring unification errors.
  let scopedSolve = scoped $ buildScoped
                    $ zonk =<< instantiateAndCheck ctx ty =<< dict
  res <- (Right <$> scopedSolve) `catchError` (return . Left)
  case res of
    Left _ -> return ([], SynthFoundAll)
    Right (block, localEnv) -> do
      currentEnv <- look
      -- Did we bind any type variables in the requested type? If so, we can't
      -- be sure this will be a match.
      let sure = null (unsolved currentEnv `envIntersect` solverSub localEnv)
      if sure then do
        logInfo SynthPass $
          "Found confident solution to " <> pprint ty
          <> " using " <> pprint name <> "."
          <> "\n  Solution:" <> pprint block
          <> "\n  New inference variables:" <> pprint (solverVars localEnv)
        let thunk = Lam $ makeAbs (Ignore UnitTy) (PureArrow, block) 
        return ([(name, thunk, localEnv)], SynthFoundAll)
      else do
        logInfo SynthPass $ "Found possible future solution to " <> pprint ty <> " using " <> pprint name
        return ([], SynthCouldFindMore)

instantiateAndCheck :: (MonadCat SolverEnv m, MonadEmbed m, MonadError Err m)
                    => SrcCtx -> Type -> Atom -> m Atom
instantiateAndCheck ctx ty x = do
  x' <- instantiateSigma ctx x
  constrainEq ty (getType x')
  return x'

-- === unification ===

constrainEq :: (MonadCat SolverEnv m, MonadError Err m)
             => Type -> Type -> m ()
constrainEq t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  let ((t1Pretty, t2Pretty), infVars) = renameForPrinting (t1', t2')
  let msg =   "Expected: " ++ pprint t1Pretty
         ++ "\n  Actual: " ++ pprint t2Pretty
         ++ (if null infVars then "" else
               "\n(Solving for: " ++ pprint infVars ++ ")")
  addContext msg $ unify t1' t2'

unify :: (MonadCat SolverEnv m, MonadError Err m)
       => Type -> Type -> m ()
unify t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  vs <- looks solverVars
  case (t1', t2') of
    _ | t1' == t2' -> return ()
    (t, Var v) | v `isin` vs -> bindQ v t
    (Var v, t) | v `isin` vs -> bindQ v t
    (Pi piTy, Pi piTy') -> do
       unify (absArgType piTy) (absArgType piTy')
       let v = Var $ freshSkolemVar (piTy, piTy') (absArgType piTy)
       -- TODO: think very hard about the leak checks we need to add here
       let (arr , resultTy ) = applyAbs piTy  v
       let (arr', resultTy') = applyAbs piTy' v
       when (void arr /= void arr') $ throw TypeErr ""
       unify resultTy resultTy'
       unifyEff (arrowEff arr) (arrowEff arr')
    (RecordTy  items, RecordTy  items') ->
      unifyExtLabeledItems items items'
    (VariantTy items, VariantTy items') ->
      unifyExtLabeledItems items items'
    (TypeCon f xs, TypeCon f' xs')
      | f == f' && length xs == length xs' -> zipWithM_ unify xs xs'
    (TC con, TC con') | void con == void con' ->
      zipWithM_ unify (toList con) (toList con')
    (Eff eff, Eff eff') -> unifyEff eff eff'
    _ -> throw TypeErr ""

unifyExtLabeledItems :: (MonadCat SolverEnv m, MonadError Err m)
  => ExtLabeledItems Type Name -> ExtLabeledItems Type Name -> m ()
unifyExtLabeledItems r1 r2 = do
  r1' <- zonk r1
  r2' <- zonk r2
  vs <- looks solverVars
  case (r1', r2') of
    _ | r1' == r2' -> return ()
    (r, Ext NoLabeledItems (Just v)) | v `isin` vs ->
      bindQ (v:>LabeledRowKind) (LabeledRow r)
    (Ext NoLabeledItems (Just v), r) | v `isin` vs ->
      bindQ (v:>LabeledRowKind) (LabeledRow r)
    (_, Ext NoLabeledItems _) -> throw TypeErr ""
    (Ext NoLabeledItems _, _) -> throw TypeErr ""
    (Ext (LabeledItems items1) t1, Ext (LabeledItems items2) t2) -> do
      let unifyPrefixes tys1 tys2 = mapM (uncurry unify) $ NE.zip tys1 tys2
      sequence_ $ M.intersectionWith unifyPrefixes items1 items2
      let diffDrop xs ys = NE.nonEmpty $ NE.drop (length ys) xs
      let extras1 = M.differenceWith diffDrop items1 items2
      let extras2 = M.differenceWith diffDrop items2 items1
      newTail <- freshInferenceName LabeledRowKind
      unifyExtLabeledItems (Ext NoLabeledItems t1)
                           (Ext (LabeledItems extras2) (Just newTail))
      unifyExtLabeledItems (Ext NoLabeledItems t2)
                           (Ext (LabeledItems extras1) (Just newTail))

unifyEff :: (MonadCat SolverEnv m, MonadError Err m)
         => EffectRow -> EffectRow -> m ()
unifyEff r1 r2 = do
  r1' <- zonk r1
  r2' <- zonk r2
  vs <- looks solverVars
  case (r1', r2') of
    _ | r1' == r2' -> return ()
    (r, EffectRow effs (Just v)) | S.null effs && v `isin` vs -> bindQ (v:>EffKind) (Eff r)
    (EffectRow effs (Just v), r) | S.null effs && v `isin` vs -> bindQ (v:>EffKind) (Eff r)
    (EffectRow effs1 t1, EffectRow effs2 t2) | not (S.null effs1 || S.null effs2) -> do
      let extras1 = effs1 `S.difference` effs2
      let extras2 = effs2 `S.difference` effs1
      newRow <- freshEff
      unifyEff (EffectRow mempty t1) (extendEffRow extras2 newRow)
      unifyEff (extendEffRow extras1 newRow) (EffectRow mempty t2)
    _ -> throw TypeErr ""

-- === constraint solver utilities ===

unsolved :: SolverEnv -> Env Kind
unsolved SolverEnv{solverVars=scope, solverSub=sub} = scope `envDiff` sub

unsolvedDicts :: SolverEnv -> Env (Scope, SrcCtx, Type)
unsolvedDicts SolverEnv{wantedDictVars=wanted, solverSub=sub} =
  wanted `envDiff` sub

zonk :: (Subst a, MonadCat SolverEnv m) => a -> m a
zonk x = do
  s <- looks solverSub
  return $ scopelessSubst s x

hasSkolems :: Subst a => a -> Bool
hasSkolems x = not $ null [() | Name Skolem _ _ <- envNames $ freeVars x]

occursIn :: Subst a => VarP v -> a -> Bool
occursIn v t = v `isin` freeVars t

renameForPrinting :: Subst a => a -> (a, [Var])
renameForPrinting x = (scopelessSubst substEnv x, newNames)
  where
    fvs = freeVars x
    infVars = filter ((== Just InferenceName) . nameSpace . varName) $ envAsVars fvs
    newNames = [ genFresh (fromString name) fvs :> fst (varAnn v)
               | (v, name) <- zip infVars nameList]
    substEnv = fold $ zipWith (\v v' -> v@>Var v') infVars newNames
    nameList = map (:[]) ['a'..'z'] ++ map show [(0::Int)..]

solveLocal :: (MonadCat SolverEnv m, MonadEmbed m, Subst a) => m a -> m a
solveLocal m = do
  (ans, env) <- scoped $ do
    -- This might get expensive. TODO: revisit once we can measure performance.
    (ans, embedEnv) <- zonk =<< embedScoped m
    embedExtend embedEnv
    return ans
  extend $ SolverEnv (unsolved env) (unsolvedDicts env) (solverSub env `envDiff` unsolved env)
  return ans

checkLeaks :: ( MonadCat SolverEnv m, MonadEmbed m, MonadError Err m
              , HasType a, Subst a) => [Var] -> m a -> m a
checkLeaks tvs m = do
  scope <- getScope
  (ans, env) <- scoped $ solveLocal m
  let resultTypeLeaks = filter (\case (Name InferenceName _ _) -> False; _ -> True) $
                          envNames $ freeVars (getType ans) `envDiff` scope
  unless (null resultTypeLeaks) $
    throw TypeErr $ "Leaked local variable `" ++ pprint (head resultTypeLeaks) ++
                    "` in result type " ++ pprint (getType ans)
  forM_ (solverSub env) $ \ty ->
    forM_ tvs $ \tv ->
      throwIf (tv `occursIn` ty) TypeErr $ "Leaked type variable: " ++ pprint tv
  extend env
  return ans

typeReduceScoped :: MonadEmbed m => m Atom -> m (Maybe Atom)
typeReduceScoped m = do
  block <- buildScoped m
  scope <- getScope
  return $ typeReduceBlock scope block

emitZonked :: (MonadCat SolverEnv m, MonadEmbed m) => Expr -> m Atom
emitZonked expr = zonk expr >>= emit

instantiateSigma :: (MonadCat SolverEnv m, MonadEmbed m, MonadError Err m)
                 => SrcCtx -> Atom -> m Atom
instantiateSigma ctx f = case getType f of
  Pi (Abs b (ImplicitArrow, _)) -> do
    x <- freshType $ binderType b
    ans <- emitZonked $ App f x
    instantiateSigma ctx ans
  Pi (Abs b (ClassArrow, _)) -> do
    dict <- makeClassDict ctx $ binderType b
    instantiateSigma ctx =<< emitZonked (App f dict)
  _ -> return f
