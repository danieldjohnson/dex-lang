-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Inference (inferModule, synthModule) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Foldable (fold, toList, asum)
import Data.Functor
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import Data.String (fromString)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Debug.Trace

import Syntax
import Embed  hiding (sub)
import Env
import Type
import PPrint
import Cat
import Util

type UInferM = ReaderT SubstEnv (ReaderT SrcCtx ((EmbedT (SolverT (Either Err)))))

type SigmaType = Type  -- may     start with an implicit lambda
type RhoType   = Type  -- doesn't start with an implicit lambda
data RequiredTy a = Check a | Infer

inferModule :: TopEnv -> UModule -> Except Module
inferModule scope (UModule decls) = do
  ((), (bindings, decls')) <- runUInferM mempty scope $
                                mapM_ (inferUDecl True) decls
  let bindings' = envFilter bindings $ \(_, b) -> case b of
                    DataBoundTypeCon _   -> True
                    DataBoundDataCon _ _ -> True
                    _ -> False
  return $ Module Typed decls' bindings'

runUInferM :: (Subst a, Pretty a)
           => SubstEnv -> Scope -> UInferM a -> Except (a, (Scope, Nest Decl))
runUInferM env scope m = runSolverT $
  runEmbedT (runReaderT (runReaderT m env) Nothing) scope

checkSigma :: UExpr -> SigmaType -> UInferM Atom
checkSigma expr sTy = case sTy of
  Pi piTy@(Abs _ (arrow, _))
    | arrow `elem` [ImplicitArrow, ClassArrow] -> case expr of
        WithSrc _ (ULam b arrow' body) | arrow' == void arrow ->
          checkULam b body piTy
        _ -> do
          buildLam (Bind ("a":> absArgType piTy)) arrow $ \x@(Var v) ->
            checkLeaks [v] $ checkSigma expr $ snd $ applyAbs piTy x
  _ -> checkRho expr sTy

inferSigma :: UExpr -> UInferM Atom
inferSigma (WithSrc pos expr) = case expr of
  ULam pat ImplicitArrow body -> addSrcPos pos $
    inferULam pat ImplicitArrow body
  _ ->
    inferRho (WithSrc pos expr)

checkRho :: UExpr -> RhoType -> UInferM Atom
checkRho expr ty = checkOrInferRho expr (Check ty)

inferRho :: UExpr -> UInferM Atom
inferRho expr = checkOrInferRho expr Infer

instantiateSigma :: Atom -> UInferM Atom
instantiateSigma f = case getType f of
  Pi (Abs b (ImplicitArrow, _)) -> do
    x <- freshType $ binderType b
    ans <- emitZonked $ App f x
    instantiateSigma ans
  Pi (Abs b (ClassArrow, _)) -> do
    ctx <- getSrcCtx
    instantiateSigma =<< emitZonked (App f (Con $ ClassDictHole ctx $ binderType b))
  _ -> return f

checkOrInferRho :: UExpr -> RequiredTy RhoType -> UInferM Atom
checkOrInferRho (WithSrc pos expr) reqTy =
 addSrcPos pos $ case expr of
  UVar v -> lookupSourceVar v >>= instantiateSigma >>= matchRequirement
  ULam (p, ann) ImplicitArrow body -> do
    argTy <- checkAnn ann
    x <- freshType argTy
    withBindPat p x $ checkOrInferRho body reqTy
  ULam b arr body -> case reqTy of
    Check ty -> do
      piTy@(Abs _ (arrReq, _)) <- fromPiType False arr ty
      checkArrow arrReq arr
      checkULam b body piTy
    Infer -> inferULam b (fmap (const Pure) arr) body
  UFor dir b body -> case reqTy of
    Check ty -> do
      Abs n (arr, a) <- fromPiType False TabArrow ty
      unless (arr == TabArrow) $
        throw TypeErr $ "Not an table arrow type: " ++ pprint arr
      allowedEff <- getAllowedEffects
      lam <- checkULam b body $ Abs n (PlainArrow allowedEff, a)
      emitZonked $ Hof $ For dir lam
    Infer -> do
      allowedEff <- getAllowedEffects
      lam <- inferULam b (PlainArrow allowedEff) body
      emitZonked $ Hof $ For dir lam
  UApp arr f x -> do
    fVal <- inferRho f
    fVal' <- zonk fVal
    piTy <- addSrcPos (srcPos f) $ fromPiType True arr $ getType fVal'
    -- Zonking twice! Once for linearity and once for the embedding. Not ideal...
    fVal'' <- zonk fVal
    xVal <- checkSigma x (absArgType piTy)
    (arr', xVal') <- case piTy of
      Abs (Ignore _) (arr', _) -> return (arr', xVal)
      _ -> do
        scope <- getScope
        let xVal' = reduceAtom scope xVal
        return (fst $ applyAbs piTy xVal', xVal')
    addEffects $ arrowEff arr'
    appVal <- emitZonked $ App fVal'' xVal'
    instantiateSigma appVal >>= matchRequirement
  UPi b arr ty -> do
    -- TODO: make sure there's no effect if it's an implicit or table arrow
    -- TODO: check leaks
    b'  <- mapM checkUType b
    piTy <- buildPi b' $ \x -> extendR (b@>x) $
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
  UTabCon xs ann -> inferTabCon xs ann >>= matchRequirement
  UIndexRange low high -> do
    n <- freshType TyKind
    low'  <- mapM (flip checkRho n) low
    high' <- mapM (flip checkRho n) high
    matchRequirement $ TC $ IndexRange n low' high'
  UHole -> case reqTy of
    Infer -> throw MiscErr "Can't infer type of hole"
    Check ty -> freshType ty
  UPrimExpr prim -> do
    prim' <- traverse lookupName prim
    val <- case prim' of
      TCExpr  e -> return $ TC e
      ConExpr e -> return $ Con e
      OpExpr  e -> emitZonked $ Op e
      HofExpr e -> emitZonked $ Hof e
    matchRequirement val
    where lookupName v = asks (! (v:>()))
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
  UCharLit x  -> matchRequirement $ CharLit $ fromIntegral $ fromEnum x
  USugar sugar -> do
    -- sugar' <- mapM inferRho sugar
    matchRequirement =<< desugar sugar
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
      case envLookup scope (v':>()) of
        Just (_, DataBoundTypeCon def    ) -> return $ TypeCon def []
        Just (_, DataBoundDataCon def con) -> return $ DataCon def [] con []
        Just (ty, _) -> return $ Var $ v':>ty
        Nothing -> throw UnboundVarErr $ pprint $ asGlobal $ varName v

-- TODO: de-dup with `bindPat`
unpackTopPat :: LetAnn -> UPat -> Expr -> UInferM ()
unpackTopPat letAnn (WithSrc _ pat) expr = case pat of
  UPatBinder b -> do
    let b' = binderAsGlobal b
    scope <- getScope
    when (b' `isin` scope) $ throw RepeatedVarErr $ pprint $ getName b'
    void $ emitTo (binderNameHint b') letAnn expr
  UPatUnit -> return () -- TODO: change if we allow effects at the top level
  UPatPair p1 p2 -> do
    val  <- emit expr
    x1   <- lift $ getFst val
    x2   <- lift $ getSnd val
    unpackTopPat letAnn p1 (Atom x1)
    unpackTopPat letAnn p2 (Atom x2)
  UPatCon conName ps -> do
    (def@(DataDef _ paramBs cons), con) <- lookupDataCon conName
    when (length cons /= 1) $ throw TypeErr $
      "sum type constructor in can't-fail pattern"
    let DataConDef _ argBs = cons !! con
    when (length argBs /= length ps) $ throw TypeErr $
      "Unexpected number of pattern binders. Expected " ++ show (length argBs)
                                             ++ " got " ++ show (length ps)
    params <- mapM (freshType . binderType) paramBs
    constrainEq (TypeCon def $ toList params) (getType expr)
    xs <- zonk expr >>= emitUnpack
    zipWithM_ (\p x -> unpackTopPat letAnn p (Atom x)) (toList ps) xs
  UPatRecord (Ext items Nothing) -> do
    RecordTy (NoExt types) <- pure $ getType expr
    when (fmap (const ()) items /= fmap (const ()) types) $ throw TypeErr $
      "Labels in record pattern do not match record type. Expected structure "
      ++ pprint (RecordTy $ NoExt types)
    xs <- zonk expr >>= emitUnpack
    zipWithM_ (\p x -> unpackTopPat letAnn p (Atom x)) (toList items) xs
  UPatRecord (Ext pats (Just tailPat)) -> do
    wantedTypes <- lift $ mapM (const $ freshType TyKind) pats
    restType <- lift $ freshInferenceName LabeledRowKind
    let vty = getType expr
    lift $ constrainEq (RecordTy $ Ext wantedTypes $ Just restType) vty
    -- Split the record.
    wantedTypes' <- lift $ zonk wantedTypes
    val <- emit =<< zonk expr
    split <- emit $ Op $ RecordSplit wantedTypes' val
    [left, right] <- getUnpacked split
    leftVals <- getUnpacked left
    zipWithM_ (\p x -> unpackTopPat letAnn p (Atom x)) (toList pats) leftVals
    unpackTopPat letAnn tailPat (Atom right)
  UPatVariant _ _ _ -> throw TypeErr "Variant not allowed in can't-fail pattern"
  UPatVariantLift _ _ -> throw TypeErr "Variant not allowed in can't-fail pattern"

inferUDecl :: Bool -> UDecl -> UInferM SubstEnv
inferUDecl topLevel (ULet letAnn (p, ann) rhs) = do
  val <- case ann of
    Nothing -> inferSigma rhs
    Just ty -> checkUType ty >>= checkSigma rhs
  expr <- zonk $ Atom val
  if topLevel
    then unpackTopPat letAnn p expr $> mempty
    else do
      -- TODO: non-top-level annotations?
      val' <- withPatHint p $ emitAnn PlainLet expr
      bindPat p val'
inferUDecl True (UData tc dcs) = do
  (tc', paramBs) <- inferUConDef tc
  let paramVars = map (\(Bind v) -> v) $ toList paramBs  -- TODO: refresh things properly
  (dcs', _) <- embedScoped $
    extendR (newEnv paramBs (map Var paramVars)) $ do
      extendScope (foldMap binderBinding paramBs)
      mapM inferUConDef dcs
  let dataDef = DataDef tc' paramBs $ map (uncurry DataConDef) dcs'
  let tyConTy = getType $ TypeCon dataDef []
  extendScope $ tc' @> (tyConTy, DataBoundTypeCon dataDef)
  forM_ (zip [0..] dcs') $ \(i, (dc,_)) -> do
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
  extendScope (binderBinding b')
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
                      checkSigma body $ snd $ applyAbs piTy x

checkUEff :: EffectRow -> UInferM EffectRow
checkUEff (EffectRow effs t) = do
   effs' <- forM effs $ \(effName, region) -> (effName,) <$> lookupVarName TyKind region
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
checkCasePat (WithSrc pos pat) scrutineeTy = addSrcPos pos $ case pat of
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

bindPat' :: UPat -> Atom -> CatT (Env ()) UInferM SubstEnv
bindPat' (WithSrc pos pat) val = addSrcContext (Just pos) $ case pat of
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
  reduced <- reduceScoped $ withEffects Pure $ checkRho ty TyKind
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

inferTabCon :: [UExpr] -> Maybe UType -> UInferM Atom
inferTabCon xs ann = do
  (n, ty) <- inferTabTy xs ann
  let tabTy = n==>ty
  xs' <- mapM (flip checkRho ty) xs
  emitZonked $ Op $ TabCon tabTy xs'

inferTabTy :: [UExpr] -> Maybe UType -> UInferM (Type, Type)
inferTabTy xs ann = case ann of
  Just ty -> do
    ty' <- checkUType ty
    case ty' of
      TabTy b a -> do
        unless (indexSetConcreteSize (binderType b) == Just (length xs)) $
           throw TypeErr $ "Table size doesn't match annotation"
        return (binderType b, a)
      _ -> throw TypeErr $ "Table constructor annotation must be a table type"
  Nothing -> case xs of
   [] -> throw TypeErr $ "Empty table constructor must have type annotation"
   (x:_) -> do
    ty <- getType <$> inferRho x
    return (FixedIntRange 0 (fromIntegral $ length xs), ty)

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

emitZonked :: Expr -> UInferM Atom
emitZonked expr = zonk expr >>= emit

addEffects :: EffectRow -> UInferM ()
addEffects eff = do
  eff' <- openEffectRow eff
  allowedEffects <- getAllowedEffects
  constrainEq (Eff allowedEffects) (Eff eff')

openEffectRow :: EffectRow -> UInferM EffectRow
openEffectRow (EffectRow effs Nothing) = extendEffRow effs <$> freshEff
openEffectRow effRow = return effRow

binderAsGlobal :: BinderP a -> BinderP a
binderAsGlobal (Ignore ann) = Ignore ann
binderAsGlobal (Bind (v:>ann)) = Bind $ asGlobal v :> ann

addSrcPos :: SrcPos -> UInferM a -> UInferM a
addSrcPos pos m = do
  env <- ask
  addSrcContext (Just pos) $ lift $
    local (const (Just pos)) $ runReaderT m env

getSrcCtx :: UInferM SrcCtx
getSrcCtx = lift ask

-- === desugaring ===

-- Fallback for optional expressions.
inferOrUseGlobal :: Tag -> Maybe UExpr -> UInferM Atom
inferOrUseGlobal name Nothing =
  instantiateSigma =<< lookupSourceVar (GlobalName name:>())
inferOrUseGlobal _ (Just item) = inferRho item

-- Unpack a lens or prism, constraining it to be correct.
unpackOptic :: Text -> Atom -> UInferM (Atom -> UInferM Atom, Atom -> UInferM Atom)
unpackOptic opticName optic = do
  TypeCon opticDef [] <- lookupSourceVar (GlobalName opticName :>())
  params <- replicateM 3 (freshType TyKind)
  constrainEq (getType optic) (TypeCon opticDef params)
  [arg] <- getUnpacked =<< zonk optic
  [build, split] <- getUnpacked arg
  return (\v -> emit $ App split v, \v -> emit $ App build v)

-- Extract specific fields from a record.
getRecordFields :: LabeledItems a -> Atom -> UInferM (LabeledItems Atom, Atom)
getRecordFields wanted record = do
  wantedTypes <- mapM (const $ freshType TyKind) wanted
  rest <- freshInferenceName LabeledRowKind
  constrainEq (getType record) (RecordTy $ Ext wantedTypes $ Just rest)
  record' <- zonk record
  [l, r] <- getUnpacked =<< emit (Op $ RecordSplit wantedTypes record')
  ls <- getUnpacked l
  return (restructure ls wanted, r)

recordCons :: LabeledItems Atom -> Atom -> UInferM Atom
recordCons fields rest = do
  row <- freshInferenceName LabeledRowKind
  constrainEq (getType rest) (RecordTy $ Ext NoLabeledItems $ Just row)
  emitOp . RecordCons fields =<< zonk rest

-- Make a lens. split maps the original atom to a pair, and build maps the
-- components back to the original.
makeLens :: (Atom -> UInferM (Atom, Atom))
          -> (Atom -> Atom -> UInferM Atom) -> UInferM Atom
makeLens split build = do
  [full, focus, ignore] <- replicateM 3 $ freshType TyKind
  let outTy = PairTy focus ignore
  split'@(Lam (Abs _ (_, splitBody))) <- buildLam (Ignore full) PureArrow $
    \atom -> do {(l, r) <- split atom; return $ Con $ PairCon l r}
  build'@(Lam (Abs _ (_, buildBody))) <- buildLam (Ignore outTy) PureArrow $
    \atom -> do {(l, r) <- getPair atom; build l r}
  constrainEq (getType splitBody) outTy
  constrainEq (getType buildBody) full
  (def, con) <- lookupDataCon (GlobalName "MkIsoLens")
  return $ DataCon def [full, focus, ignore] con [
    Record $ labeledSingleton "split" split'
          <> labeledSingleton "build" build']

makeLeft :: Atom -> UInferM Atom
makeLeft x = do
  rty <- freshType TyKind
  DataCon eitherDef _ i _ <- lookupSourceVar (GlobalName "Left" :>())
  return $ DataCon eitherDef [getType x, rty] i [x]

makeRight :: Atom -> UInferM Atom
makeRight x = do
  lty <- freshType TyKind
  DataCon eitherDef _ i _ <- lookupSourceVar (GlobalName "Right" :>())
  return $ DataCon eitherDef [lty, getType x] i [x]

makeVariant :: LabeledItems a -> Label -> Atom -> UInferM Atom
makeVariant skip label atom = do
  rest <- freshInferenceName LabeledRowKind
  prefix <- mapM (const $ freshType TyKind) skip
  let known = prefix <> (labeledSingleton label $ getType atom)
  return $ Variant (Ext known $ Just rest) label 0 atom

liftVariant :: LabeledItems a -> Atom -> UInferM Atom
liftVariant skip atom = do
  prefix <- mapM (const $ freshType TyKind) skip
  emitOp $ VariantLift prefix atom

constrainedAs :: Type -> Atom -> UInferM Atom
constrainedAs ty atom = constrainEq (getType atom) ty *> return atom

-- Match on a Dex (a | b) with a Haskell function.
matchEither :: (Either Atom Atom -> UInferM Atom)
            -> (Atom -> UInferM Atom)
matchEither fn atom = do
  [lty, rty, resultTy] <- replicateM 3 $ freshType TyKind
  TypeCon eitherDef [] <- lookupSourceVar (GlobalName "(|)" :>())
  constrainEq (getType atom) (TypeCon eitherDef [lty, rty])
  leftAlt <- buildNAbs (toNest [Ignore lty]) $
    \[l] -> constrainedAs resultTy =<< fn (Left l)
  rightAlt <- buildNAbs (toNest [Ignore rty]) $
    \[r] -> constrainedAs resultTy =<< fn (Right r)
  emit $ Case atom [leftAlt, rightAlt] resultTy

-- Match on a Dex variant with a LabeledItems of cases and a fallback.
matchVariantFields :: LabeledItems (Atom -> UInferM Atom)
                   -> (Atom -> UInferM Atom) -> Atom -> UInferM Atom
matchVariantFields matchers fallback variant = do
  matchedTypes <- mapM (const $ freshType TyKind) matchers
  rest <- freshInferenceName LabeledRowKind
  constrainEq (getType variant) (VariantTy $ Ext matchedTypes $ Just rest)
  variant' <- zonk variant
  variant'' <- emit $ Op $ VariantSplit matchedTypes variant'
  resultTy <- freshType TyKind
  alts <- flip mapM (zip (toList matchers) (toList matchedTypes)) $
    \(fn, vty) -> buildNAbs (toNest [Ignore vty]) $
      \[v] -> constrainedAs resultTy =<< fn v
  knownAlt <- buildNAbs
    (toNest [Ignore $ VariantTy $ Ext matchedTypes Nothing]) $
    \[v] -> emit $ Case v alts resultTy
  fallbackAlt <- buildNAbs
    (toNest [Ignore $ VariantTy $ Ext NoLabeledItems $ Just rest]) $
    \[v] -> constrainedAs resultTy =<< fallback v
  emit $ Case variant'' [knownAlt, fallbackAlt] resultTy

makePrism :: (Atom -> UInferM Atom)
          -> (Atom -> UInferM Atom) -> UInferM Atom
makePrism split build = do
  [full, focus, ignore] <- replicateM 3 $ freshType TyKind
  TypeCon eitherDef [] <- lookupSourceVar (GlobalName "(|)" :>())
  let outTy = TypeCon eitherDef [focus, ignore]
  split'@(Lam (Abs _ (_, splitBody))) <- buildLam (Ignore full) PureArrow split
  build'@(Lam (Abs _ (_, buildBody))) <- buildLam (Ignore outTy) PureArrow build
  constrainEq (getType splitBody) outTy
  constrainEq (getType buildBody) full
  (def, con) <- lookupDataCon (GlobalName "MkIsoPrism")
  return $ DataCon def [full, focus, ignore] con [
    Record $ labeledSingleton "split" split'
          <> labeledSingleton "build" build']

desugar :: USugar -> UInferM Atom
desugar sugar = case sugar of
    -- #foo desugars to
    -- MkIsoLens {split=\{foo, ...r}. (foo, r), build=\(foo,r). {foo, ...r}}
    ULensRecordField label -> let
      split atom = do
        (l, r) <- getRecordFields (labeledSingleton label ()) atom
        Just (l', NoLabeledItems) <- return $ popLabeled label l
        return (l', r)
      build left right =
        recordCons (labeledSingleton label left) right
      in makeLens split build
    -- {foo & bar:barLens & ...restLens} desugars to
    -- MkIsoLens { split=\{foo, bar, ...r}. ( { foo
    --                                        , bar=fst $ splitLens barLens bar
    --                                        , ...(fst $ splitLens restLens r)}
    --                                      , { bar=snd $ splitLens barLens bar
    --                                        , ...(snd $ splitLens restLens r)}
    --             build=\({foo, bar=barL, ...rL}, {bar=barR, ...rR}).
    --                        {foo, bar=buildLens barLens (barL, barR),
    --                         ...(buildLens restLens (rL, rR))}
    --           }
    ULensRecord (Ext lenses restLens) -> do
      restLens' <- inferOrUseGlobal "lensNone" restLens
      (restSplit, restBuild) <- unpackOptic "IsoLens" restLens'
      let step (ignoreFields, splitter, builder) (label, _, lens) =
            case lens of
              Just lens' -> do
                -- {foo:fooLens & ...} case: split with the provided optic.
                (lensSplit, lensBuild) <- unpackOptic "IsoLens" =<< inferRho lens'
                let splitter' atoms = do
                        Just (v, vs) <- return $ popLabeled label atoms
                        (l, r) <- getPair =<< lensSplit v
                        (ls, rs) <- splitter vs
                        return $ ( labeledSingleton label l <> ls
                                 , labeledSingleton label r <> rs)
                    builder' left right = do
                        Just (l, ls) <- return $ popLabeled label left
                        Just (r, rs) <- return $ popLabeled label right
                        v <- lensBuild $ Con $ PairCon l r
                        vs <- builder ls rs
                        return $ labeledSingleton label v <> vs
                return ( labeledSingleton label () <> ignoreFields
                       , splitter'
                       , builder')
              -- {foo & ...} case: put entire axis into the focus.
              Nothing -> return (ignoreFields, splitter', builder') where
                splitter' atoms = do
                  Just (v, vs) <- return $ popLabeled label atoms
                  (fs, is) <- splitter vs
                  return (labeledSingleton label v <> fs, is)   
                builder' left right = do
                  Just (l, ls) <- return $ popLabeled label left
                  vs <- builder ls right
                  return $ labeledSingleton label l <> vs
      -- Fold over the fields in reverse order (so we can push and pop).
      (ignoreFields, splitter, builder) <- foldM step
        ( NoLabeledItems
        , const $ return (NoLabeledItems, NoLabeledItems)
        , const $ const $ return NoLabeledItems)
        (reverse $ toList $ withLabels lenses)
      let split atom = do
            (known, rest) <- getRecordFields lenses atom
            (fs, is) <- splitter known
            (fr, ir) <- getPair =<< restSplit rest
            left <- recordCons fs fr
            right <- recordCons is ir
            return (left, right)
      let build left right = do
            (fs, fr) <- getRecordFields lenses left
            (is, ir) <- getRecordFields ignoreFields right
            known <- builder fs is
            rest <- restBuild $ Con $ PairCon fr ir
            recordCons known rest
      makeLens split build
    -- #!foo desugars to
    -- MkIsoPrism { split=\v. case v of {|foo=x|}    -> Left x
    --                                  {|foo|...y|} -> Right y
    --            , build=\v. case v of Left x  -> {|foo=x|}
    --                                  Right y -> {|foo|...y|} }
    UPrismVariantField label -> let
      split = matchVariantFields (labeledSingleton label makeLeft) makeRight 
      build = matchEither $ \case
        Left v -> makeVariant NoLabeledItems label v
        Right v -> liftVariant (labeledSingleton label ()) v
      in makePrism split build
    -- #!{foo | bar:barPrism | ...restPrism} desugars to something like
    -- MkIsoPrism { split=\v. case v of
    --                 {|foo=x|} -> Left {|foo=x|}
    --                 {|bar=x|} -> case splitPrism barPrism x of
    --                                 Left y  -> Left  {|bar=y|}
    --                                 Right y -> Right {|bar=y|}
    --                 {|foo|bar|...x|} -> case splitPrism restPrism x of
    --                                 Left y  -> Left  {|foo|bar|...y|}
    --                                 Right y -> Right {|foo|bar|...y|}
    --            , build=\v. case v of
    --                 Left {|foo=x|} -> {|foo=x|}
    --                 Left {|bar=x|} -> {|bar=buildPrism barPrism $ Left x |}
    --                 Left {|foo|bar|...x|} ->
    --                   {|foo|bar|...buildPrism barPrism $ Left x|}
    --                 Right {|bar=x|} -> {|bar=buildPrism barPrism $ Right x |}
    --                 Right {|foo|bar|...x|} ->
    --                   {|foo|bar|...buildPrism barPrism $ Right x|}
    --            }
    UPrismVariant (Ext prisms restPrism) -> do
      restPrism' <- inferOrUseGlobal "prismNone" restPrism
      (restSplit, restBuild) <- unpackOptic "IsoPrism" restPrism'
      let step (splitters, leftBuilders, rightBuilders) (label, _, prism) =
            case prism of
              Just prism' -> do
                -- {foo:fooPrism | ...} case: split with the provided optic.
                (prismSplit, prismBuild) <-
                    unpackOptic "IsoPrism" =<< inferRho prism'
                let
                  -- Note: the labels in leftBuilders/rightBuilders are the ones
                  -- we need to lift over when splitting something to the
                  -- left/right; conversely the labels in splitters are the ones
                  -- we need to lift over when building something.
                  splitter = labeledSingleton label $ \v -> do
                    v' <- prismSplit v
                    flip matchEither v' $ \case
                      Left l  -> makeLeft  =<< makeVariant leftBuilders label l
                      Right r -> makeRight =<< makeVariant rightBuilders label r
                  leftBuilder = labeledSingleton label $ \l ->
                    makeVariant splitters label =<< prismBuild =<< makeLeft l
                  rightBuilder = labeledSingleton label $ \r -> do
                    makeVariant splitters label =<< prismBuild =<< makeRight r
                return ( splitters <> splitter
                       , leftBuilders <> leftBuilder
                       , rightBuilders <> rightBuilder)
              -- {foo | ...} case: put entire slice into the focus.
              Nothing -> let
                splitter = labeledSingleton label $ \v ->
                  makeLeft =<< makeVariant leftBuilders label v
                leftBuilder = labeledSingleton label $ \l ->
                  makeVariant splitters label l
                in return ( splitters <> splitter
                          , leftBuilders <> leftBuilder
                          , rightBuilders)
      -- Fold over the fields in forward order (so we know what fields to skip).
      (splitters, leftBuilders, rightBuilders) <- foldM step
        (NoLabeledItems, NoLabeledItems, NoLabeledItems)
        (toList $ withLabels prisms)
      let split = matchVariantFields splitters $ \v -> do
            v' <- restSplit v
            flip matchEither v' $ \case
              Left l -> makeLeft =<< liftVariant leftBuilders l
              Right r -> makeRight =<< liftVariant rightBuilders r
      let build = matchEither $ \case
            Left l -> matchVariantFields leftBuilders
              (\v -> liftVariant splitters =<< restBuild =<< makeLeft v) l
            Right r -> matchVariantFields rightBuilders
              (\v -> liftVariant splitters =<< restBuild =<< makeRight v) r
      makePrism split build
    -- TODO: record prisms
    UPrismRecord _ -> do
      throw NotImplementedErr "!"

-- === typeclass dictionary synthesizer ===

-- We have two variants here because at the top level we want error messages and
-- internally we want to consider all alternatives.
type SynthPassM = SubstEmbedT (Either Err)
type SynthDictM = SubstEmbedT []

synthModule :: Scope -> Module -> Except Module
synthModule scope (Module Typed decls bindings) = do
  decls' <- fst <$> runSubstEmbedT
              (traverseDecls (traverseHoles synthDictTop) decls) scope
  return $ Module Core decls' bindings
synthModule _ _ = error $ "Unexpected IR variant"

synthDictTop :: SrcCtx -> Type -> SynthPassM Atom
synthDictTop ctx ty = do
  scope <- getScope
  let solutions = runSubstEmbedT (synthDict ty) scope
  addSrcContext ctx $ case solutions of
    [] -> throw TypeErr $ "Couldn't synthesize a class dictionary for: " ++ pprint ty
    [(ans, env)] -> embedExtend env $> ans
    _ -> throw TypeErr $ "Multiple candidate class dictionaries for: " ++ pprint ty
           ++ "\n" ++ pprint solutions

traverseHoles :: (MonadReader SubstEnv m, MonadEmbed m)
              => (SrcCtx -> Type -> m Atom) -> TraversalDef m
traverseHoles fillHole = (traverseDecl recur, traverseExpr recur, synthPassAtom)
  where
    synthPassAtom atom = case atom of
      Con (ClassDictHole ctx ty) -> fillHole ctx ty
      _ -> traverseAtom recur atom
    recur = traverseHoles fillHole

synthDict :: Type -> SynthDictM Atom
synthDict ty = do
  (d, bindingInfo) <- getBinding
  case bindingInfo of
    LetBound InstanceLet _ -> do
      block <- buildScoped $ inferToSynth $ instantiateAndCheck ty d
      traverseBlock (traverseHoles (const synthDict)) block >>= emitBlock
    LamBound ClassArrow -> do
      d' <- superclass d
      inferToSynth $ instantiateAndCheck ty d'
    _ -> empty

-- TODO: this doesn't de-dup, so we'll get multiple results if we have a
-- diamond-shaped hierarchy.
superclass :: Atom -> SynthDictM Atom
superclass dict = return dict <|> do
  (f, LetBound SuperclassLet _) <- getBinding
  inferToSynth $ tryApply f dict

getBinding :: SynthDictM (Atom, BinderInfo)
getBinding = do
  scope <- getScope
  (v, (ty, bindingInfo)) <- asum $ map return $ envPairs scope
  return (Var (v:>ty), bindingInfo)

inferToSynth :: (Pretty a, Subst a) => UInferM a -> SynthDictM a
inferToSynth m = do
  scope <- getScope
  case runUInferM mempty scope m of
    Left _ -> empty
    Right (x, (_, decls)) -> do
      mapM_ emitDecl decls
      return x

tryApply :: Atom -> Atom -> UInferM Atom
tryApply f x = do
  f' <- instantiateSigma f
  Pi (Abs b _) <- return $ getType f'
  constrainEq (binderType b) (getType x)
  emitZonked $ App f' x

instantiateAndCheck :: Type -> Atom -> UInferM Atom
instantiateAndCheck ty x = do
  x' <- instantiateSigma x
  constrainEq ty (getType x')
  return x'

-- === constraint solver ===

data SolverEnv = SolverEnv { solverVars :: Env Kind
                           , solverSub  :: Env Type }
type SolverT m = CatT SolverEnv m

runSolverT :: (MonadError Err m, Subst a, Pretty a)
           => CatT SolverEnv m a -> m a
runSolverT m = liftM fst $ flip runCatT mempty $ do
   ans <- m >>= zonk
   applyDefaults
   ans' <- zonk ans
   vs <- looks $ envNames . unsolved
   throwIf (not (null vs)) TypeErr $ "Ambiguous type variables: "
                                   ++ pprint vs ++ "\n\n" ++ pprint ans'
   return ans'

applyDefaults :: MonadCat SolverEnv m => m ()
applyDefaults = do
  vs <- looks unsolved
  forM_ (envPairs vs) $ \(v, k) -> case k of
    EffKind -> addSub v $ Eff Pure
    _ -> return ()
  where addSub v ty = extend $ SolverEnv mempty (v@>ty)

solveLocal :: Subst a => UInferM a -> UInferM a
solveLocal m = do
  (ans, env@(SolverEnv freshVars sub)) <- scoped $ do
    -- This might get expensive. TODO: revisit once we can measure performance.
    (ans, embedEnv) <- zonk =<< embedScoped m
    embedExtend embedEnv
    return ans
  extend $ SolverEnv (unsolved env) (sub `envDiff` freshVars)
  return ans

checkLeaks :: Subst a => [Var] -> UInferM a -> UInferM a
checkLeaks tvs m = do
  (ans, env) <- scoped $ solveLocal $ m
  forM_ (solverSub env) $ \ty ->
    forM_ tvs $ \tv ->
      throwIf (tv `occursIn` ty) TypeErr $ "Leaked type variable: " ++ pprint tv
  extend env
  return ans

unsolved :: SolverEnv -> Env Kind
unsolved (SolverEnv vs sub) = vs `envDiff` sub

freshInferenceName :: (MonadError Err m, MonadCat SolverEnv m) => Kind -> m Name
freshInferenceName k = do
  env <- look
  let v = genFresh (rawName InferenceName "?") $ solverVars env
  extend $ SolverEnv (v@>k) mempty
  return v

freshType ::  (MonadError Err m, MonadCat SolverEnv m) => Kind -> m Type
freshType EffKind = Eff <$> freshEff
freshType k = Var . (:>k) <$> freshInferenceName k

freshEff :: (MonadError Err m, MonadCat SolverEnv m) => m EffectRow
freshEff = EffectRow [] . Just <$> freshInferenceName EffKind

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

zonk :: (Subst a, MonadCat SolverEnv m) => a -> m a
zonk x = do
  s <- looks solverSub
  return $ scopelessSubst s x

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
    (r, EffectRow [] (Just v)) | v `isin` vs -> bindQ (v:>EffKind) (Eff r)
    (EffectRow [] (Just v), r) | v `isin` vs -> bindQ (v:>EffKind) (Eff r)
    (EffectRow effs1@(_:_) t1, EffectRow effs2@(_:_) t2) -> do
      let extras1 = effs1 `setDiff` effs2
      let extras2 = effs2 `setDiff` effs1
      newRow <- freshEff
      unifyEff (EffectRow [] t1) (extendEffRow extras2 newRow)
      unifyEff (extendEffRow extras1 newRow) (EffectRow [] t2)
    _ -> throw TypeErr ""

setDiff :: Eq a => [a] -> [a] -> [a]
setDiff xs ys = filter (`notElem` ys) xs

bindQ :: (MonadCat SolverEnv m, MonadError Err m) => Var -> Type -> m ()
bindQ v t | v `occursIn` t = throw TypeErr $ "Occurs check failure: " ++ pprint (v, t)
          | hasSkolems t = throw TypeErr "Can't unify with skolem vars"
          | otherwise = extend $ mempty { solverSub = v@>t }

hasSkolems :: Subst a => a -> Bool
hasSkolems x = not $ null [() | Name Skolem _ _ <- envNames $ freeVars x]

occursIn :: Subst a => Var -> a -> Bool
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

instance Semigroup SolverEnv where
  -- TODO: as an optimization, don't do the subst when sub2 is empty
  -- TODO: make concatenation more efficient by maintaining a reverse-lookup map
  SolverEnv scope1 sub1 <> SolverEnv scope2 sub2 =
    SolverEnv (scope1 <> scope2) (sub1' <> sub2)
    where sub1' = fmap (scopelessSubst sub2) sub1

instance Monoid SolverEnv where
  mempty = SolverEnv mempty mempty
  mappend = (<>)
