module Elaboration where

import Prelude hiding (lookup)
import Control.Monad
import qualified Data.List.NonEmpty as NE
import Text.Megaparsec

import Syntax
import Evaluation
import Conversion
import Printing

-- Elaboration
--------------------------------------------------------------------------------

type Types = [(Name, VTy)]

data Cxt = Cxt {env :: Env, types :: Types, lvl :: Lvl, pos :: SourcePos}

emptyCxt :: SourcePos -> Cxt
emptyCxt = Cxt [] [] 0

bind :: Name -> VTy -> Cxt -> Cxt
bind x ~a (Cxt env types l pos) =
  Cxt (VETm (VVar l):env) ((x, a):types) (l + 1) pos

bindLevel :: Name -> Cxt -> Cxt
bindLevel x (Cxt env types l pos) =
  Cxt (VESize (VLVar l):env) ((x, VUnit):types) (l + 1) pos

define :: Name -> VTm -> VTy -> Cxt -> Cxt
define x ~t ~a (Cxt env types l pos) =
  Cxt (VETm t:env) ((x, a):types) (l + 1) pos

type M = Either (String, SourcePos)

report :: Cxt -> String -> M a
report cxt msg = Left (msg, pos cxt)

showTm :: Cxt -> Tm -> String
showTm cxt t = prettyTm 0 (map fst (types cxt)) t []

showTy :: Cxt -> Ty -> String
showTy cxt a = prettyTy 0 (map fst (types cxt)) a []

showTm0 :: Tm -> String
showTm0 t = prettyTm 0 [] t []

showTy0 :: Ty -> String
showTy0 a = prettyTy 0 [] a []

showVal :: Cxt -> VTm -> String
showVal cxt v = showTm cxt $ quoteTm (lvl cxt) v

showVTy :: Cxt -> VTy -> String
showVTy cxt v = showTy cxt $ quoteTy (lvl cxt) v

--------------------------------------------------------------------------------

inferU :: Cxt -> Raw -> M (Tm, Size)
inferU cxt t = do
  (t', a) <- infer cxt t
  case a of
    VU i -> pure (t', quoteSize (lvl cxt) i)
    _    -> report cxt "expected a type"

isSmall :: Cxt -> Size -> VTy -> M ()
isSmall cxt i ty = do
  let vi = evalSize (env cxt) i
  case ty of
    VU j | j < vi -> pure ()
    VU j -> report cxt ("Universe " ++ showVTy cxt (VU j) ++ " is not small at level " ++ showTy cxt (U i))

    VDecode j _ | j <= vi -> pure ()
    VDecode j _ -> report cxt ("Decoded type at level " ++ showVTy cxt (VU j) ++ " is not small at level " ++ showTy cxt (U i))

    VLPi n a -> isSmall (bindLevel n cxt) i (a (VLVar (lvl cxt)))

    VPi n a b -> do
        isSmall cxt i a
        isSmall (bind n a cxt) i (b (VVar (lvl cxt)))

    VSigma n a b -> do
        isSmall cxt i a
        isSmall (bind n a cxt) i (b (VVar (lvl cxt)))

    VTensor a b -> do
        isSmall cxt i a
        isSmall cxt i b
    VUnit -> pure ()
    VDLabel _ tyInner -> isSmall cxt i tyInner

    VMu _ d -> isDescSmall cxt i d

    VEnumU -> pure ()
    VEnumT _ -> pure ()
    VSmallPiE _ _ -> pure ()

    VExt _ _ -> report cxt "Cannot prove smallness: opaque description extension"
    VSquare _ _ _ -> report cxt "Cannot prove smallness: opaque square"

isDescSmall :: Cxt -> Size -> VDesc -> M ()
isDescSmall cxt i = \case
  VDescTensor d1 d2 -> do
    isDescSmall cxt i d1
    isDescSmall cxt i d2

  VDescSum n a d -> do
    isSmall cxt i a
    isDescSmall (bind n a cxt) i (d (VVar (lvl cxt)))

  VDescProd n a d -> do
    isSmall cxt i a
    isDescSmall (bind n a cxt) i (d (VVar (lvl cxt)))

  VDescCall _ k -> case k of
    VSwitch tuple _ -> isTupleSmall cxt i tuple
    _ -> pure ()

  VDescUnit -> pure ()
  VDescVar  -> pure ()

isTupleSmall :: Cxt -> Size -> VTm -> M ()
isTupleSmall cxt i = \case
  VPair (VDReturn d) rest -> do
      isDescSmall cxt i d
      isTupleSmall cxt i rest
  VDReturn d -> isDescSmall cxt i d
  VOne -> pure ()
  _ -> pure ()

coe :: Cxt -> Lvl -> VTy -> VTy -> Tm -> M Tm
coe cxt l sourceTy targetTy m =
  if convTy l sourceTy targetTy then
    pure m
  else case (sourceTy, targetTy) of
    (VU i, VU j) | i <= j ->
      pure $ Code (quoteSize (lvl cxt) j) (Decode (quoteSize (lvl cxt) i) m)

    (VPi n1 a1 b1, VPi n2 a2 b2) -> do
      let cxt' = bind n2 a2 cxt
      let l' = lvl cxt'

      u_x <- coe cxt' l' a2 a1 (Var (Ix 0))

      let env' = env cxt'
      let vu_x = evalTm env' u_x
      let vm = evalTm (env cxt) m
      let m_u_x = quoteTm l' (vApp vm vu_x)

      n_x <- coe cxt' l' (b1 vu_x) (b2 (VVar l)) m_u_x

      pure $ Lam n2 n_x

    (VSigma n1 a1 b1, VSigma n2 a2 b2) -> do
      let vm = evalTm (env cxt) m
      let m1 = quoteTm l (applyFst vm)
      let m2 = quoteTm l (applySnd vm)

      c_m1 <- coe cxt l a1 a2 m1
      let vc_m1 = evalTm (env cxt) c_m1
      
      c_m2 <- coe cxt l (b1 (applyFst vm)) (b2 vc_m1) m2

      pure $ DPair n2 c_m1 c_m2

    (VTensor a1 b1, VTensor a2 b2) -> do
      let vm = evalTm (env cxt) m
      let m1 = quoteTm l (applyFst vm)
      let m2 = quoteTm l (applySnd vm)

      c_m1 <- coe cxt l a1 a2 m1
      c_m2 <- coe cxt l b1 b2 m2

      pure $ Pair c_m1 c_m2

    _ ->
      report cxt ("Error: Invalid coercion \n" ++ showVTy cxt sourceTy ++ "\n to \n" ++ showVTy cxt targetTy)

elabSize :: Cxt -> RawSize -> M Size
elabSize cxt = \case
  RSzVar x -> do
    let go i [] = report cxt ("Level variable out of scope: " ++ x)
        go i ((x', _):tys)
          | x == x'   = pure (LVar (Ix i))
          | otherwise = go (i + 1) tys
    go 0 (types cxt)
  RSz i -> pure (Sz i)
  RSucc s -> Succ <$> elabSize cxt s
  RBig -> pure Big
  ROmega -> pure Omega

checkTy :: Cxt -> Raw -> Size -> M Ty
checkTy cxt t size = case t of
  RSrcPos pos t -> checkTy (cxt {pos = pos}) t size

  RU s -> do
    s' <- elabSize cxt s
    if s' < size
    then pure $ U s'
    else report cxt ("Size issue: " ++ showTy cxt (U s') ++ " is too large to fit in " ++ showTy cxt (U size))

  RRecord [] -> pure Unit
  RRecord ((x, a):xs) -> do
    -- TODO : Make sure that records indeed live in the right universe
    -- Maybe just the user notation is broken : `let Category : Tp = {}`
    let nextSize = case size of
          Sz i -> Sz (i + 1)
          _  -> Omega

    aTy <- checkTy cxt a nextSize
    let cxt' = bind x (evalTy (env cxt) aTy) cxt
    bTy <- checkTy cxt' (RRecord xs) nextSize
    pure $ Sigma x aTy bTy

  RPi x a b -> do
    a' <- checkTy cxt a size
    let cxt' = bind x (evalTy (env cxt) a') cxt
    b' <- checkTy cxt' b size
    pure $ Pi x a' b'

  RLPi l a -> do
    let cxt' = bindLevel l cxt
    a' <- checkTy cxt' a size
    pure $ LPi l a'

  _ -> do
    (tTm, s) <- inferU cxt t
    if s <= size then
      pure (Decode s tTm)
    else do
      let ty = Decode s tTm
      isSmall cxt size (evalTy (env cxt) ty)
      pure ty

check :: Cxt -> Raw -> VTy -> M Tm
check cxt t a = case (t, a) of
  (RSrcPos pos t, a) -> check (cxt {pos = pos}) t a

  (RRecordVal [], VUnit) -> pure One
  
  (RRecordVal ((x, val):xs), VSigma y aTy bTy) -> do
    if x /= y then report cxt ("Expected field " ++ y ++ " but got " ++ x) else pure ()
    tTm <- check cxt val aTy
    let vt = evalTm (env cxt) tTm
    uTm <- check cxt (RRecordVal xs) (bTy vt)
    pure $ DPair x tTm uTm

  (RLam x t, VPi x' a b) ->
    Lam x <$> check (bind x a cxt) t (b (VVar (lvl cxt)))

  (RLAbs l t, VLPi _ b) -> do
    let cxt' = bindLevel l cxt
    t' <- check cxt' t (b (VLVar (lvl cxt)))
    pure $ LAbs l t'

  (_, VU s) -> do
    let sQuote = quoteSize (lvl cxt) s
    u <- checkTy cxt t sQuote
    pure $ Code sQuote u

  (ROne, VUnit) -> pure One

  (ROne, VSmallPiE VNilE _) -> pure One

  (RPair t1 t2, VSmallPiE (VConsE _ eRest) f) -> do
      let getTy (VCode _ ty) = ty
          getTy v            = VDecode VBig v

      u1 <- check cxt t1 (getTy (vApp f VZeroE))
      u2 <- check cxt t2 (VSmallPiE eRest (VLam "e" \e -> vApp f (VSuccE e)))
      pure (Pair u1 u2)

  (RPair t1 t2, VSigma x a b) -> do
      u1 <- check cxt t1 a
      u2 <- check cxt t2 (b (evalTm (env cxt) u1))
      pure (DPair x u1 u2)

  (RPair t1 t2, VTensor a b) -> do
      u1 <- check cxt t1 a
      u2 <- check cxt t2 b
      pure (Pair u1 u2)

  (RLet x aTm tTm uTm, a') -> do
    aTm' <- checkTy cxt aTm Omega
    let va = evalTy (env cxt) aTm'
    tTm' <- check cxt tTm va
    let vt = evalTm (env cxt) tTm'
    uTm' <- check (define x vt va cxt) uTm a'
    pure (Let x aTm' tTm' uTm')

  _ -> do
    (m, bTy) <- infer cxt t
    coe cxt (lvl cxt) bTy a m

-- Datatypes
--------------------------------------------------------------------------------

-- Elaborates the type of the big Pi of the parameters, returns the type, its semantics and its size (first premise of rule a)
elabDataTy :: Cxt -> [(Name, Raw)] -> Raw -> M (Ty, VTy, Size)
elabDataTy cxt params ty = do
  let tyParams_raw = foldr (\(p, pTy) acc -> RPi p pTy acc) ty params
  tyParams <- checkTy cxt tyParams_raw Omega
  let vTyParams = evalTy (env cxt) tyParams

  let getSize (U s) = s
      getSize (Decode s _) = s
      getSize (Pi _ _ b) = getSize b
      getSize _ = Big

  pure (tyParams, vTyParams, getSize tyParams)

-- Adds all the parameters in the context (Binding in the second premise of rule a)
buildParamCxt :: Cxt -> [(Name, Raw)] -> M (Cxt, [Ty])
buildParamCxt c [] = pure (c, [])
buildParamCxt c ((p, pTy):ps) = do
  pTyTm <- checkTy c pTy Omega
  let vpTy = evalTy (env c) pTyTm
  (c', pTyTms) <- buildParamCxt (bind p vpTy c) ps
  pure (c', pTyTm : pTyTms)

elabTags :: [(Name, Raw)] -> Tm
elabTags = foldr (\(cName, _) acc -> ConsE cName acc) NilE

-- Checks if the argument is recursive: rule (f)
isRec :: Name -> Raw -> Bool
isRec d (RSrcPos _ t) = isRec d t
isRec d (RVar y) = y == d
isRec d (RApp f _) = isRec d f
isRec d _ = False

-- TODO: double check this, should probably be integrated by default
checkInfRec :: Name -> Cxt -> Raw -> M (Maybe Desc)
checkInfRec dName c = \case
  RSrcPos pos t -> checkInfRec dName (c {pos = pos}) t
  RPi z dom cod -> do
    if isRec dName cod then do
      domTy <- checkTy c dom Omega
      pure $ Just (DescProd z domTy DescVar)
    else do
      domTy <- checkTy c dom Omega
      let vDom = evalTy (env c) domTy
      res <- checkInfRec dName (bind z vDom c) cod
      case res of
        Just dCod -> pure $ Just (DescProd z domTy dCod)
        Nothing -> pure Nothing
  _ -> pure Nothing

-- TODO : rethink this function, probably we can simplify it
-- Elaborates the description associated to a raw term : second premise of rule (b)
elabConstrDesc :: Name -> Cxt -> Raw -> M Desc
elabConstrDesc dName c = \case
  RSrcPos pos t -> elabConstrDesc dName (c {pos = pos}) t
  RPi y a b -> do
    if isRec dName a then do
      rest <- elabConstrDesc dName c b
      pure $ DescTensor DescVar rest
    else do
      infRecDesc <- checkInfRec dName c a
      case infRecDesc of
        Just d_a -> do
          rest <- elabConstrDesc dName c b
          pure $ DescTensor d_a rest
        Nothing -> do
          aTy <- checkTy c a Omega
          let va = evalTy (env c) aTy
          rest <- elabConstrDesc dName (bind y va c) b
          pure $ DescSum y aTy rest
  _ -> pure DescUnit

-- Elaborates the full description with all the parameters
elabFullDesc :: Name -> Int -> Ty -> Tm -> Desc
elabFullDesc dName numParams tagTy tuple =
  let paramVars = [Var (Ix i) | i <- [numParams, numParams - 1 .. 1]]
      switchTm = Switch tuple (Var 0)
      descCall = DescCall (Data dName paramVars) switchTm
  in DescSum "c" tagTy descCall

-- Elaborate constructor : rule (c)
elabConstrTm :: Name -> Name -> [(Name, Raw)] -> Raw -> Tm -> Tm
elabConstrTm dName cName params cTyRaw cTag =
  let getArgs (RSrcPos _ t) = getArgs t
      getArgs (RPi y _ b) = y : getArgs b
      getArgs _ = []
      args = getArgs cTyRaw
      numArgs = length args

      -- Rule (e, d)
      elabArg (RSrcPos _ t) idx = elabArg t idx
      elabArg (RPi y a b) idx =
        if isRec dName a then
          Pair (Var (Ix idx)) (elabArg b (idx - 1))
        else
          DPair y (Var (Ix idx)) (elabArg b (idx - 1))
      elabArg _ _ = One

      payload = elabArg cTyRaw (numArgs - 1)
      inner = ConLabel cName (In (DPair "c" cTag payload))
      body = foldr Lam inner args
  in foldr (\(p, _) acc -> Lam p acc) body params


-- Elaborates all the constructors : first premise of rule (b)
elabConstrs :: Name -> [(Name, Raw)] -> Cxt -> [((Name, Raw), Tm)] -> M (Cxt, Tm -> Tm, [(Name, Ty, Tm)])
elabConstrs dName params c [] = pure (c, id, [])
elabConstrs dName params c (((cName, cTyRaw), cTag) : rest) = do
  let fullTyRaw = foldr (\(p, pTy) acc -> RPi p pTy acc) cTyRaw params

  cTyTm <- checkTy c fullTyRaw Omega
  let term = elabConstrTm dName cName params cTyRaw cTag

  let vcTy = evalTy (env c) cTyTm
  let vcTerm = evalTm (env c) term

  (cFinal, wrapLet, constrsData) <- elabConstrs dName params (define cName vcTerm vcTy c) rest

  pure (cFinal, Let cName cTyTm term . wrapLet, (cName, cTyTm, term) : constrsData)


-- Eliminators
--------------------------------------------------------

-- Elaborates the eliminator type
elabElimTy :: VSize -> Name -> [(Name, Raw)] -> [Ty] -> Lvl -> VTm -> VTm -> VTm -> Ty
elabElimTy uLevel dName params pTyTms (Lvl l_p) vTuple vTagTm vTermD =
  let n = length params

      vParams = [VVar (Lvl i) | i <- [l_p - n .. l_p - 1]]
      vDatatypeCode = foldl vApp vTermD vParams

      vDatatype = VDecode uLevel vDatatypeCode

      vPTy = VPi "x" vDatatype (\_ -> VU VOmega)

      -- TODO : check the "hardcoded" eliminator type more carefuly
      vElimTyBody =
        VPi "P" vPTy $ \vP ->

          let mBody vc =
                let vDesc_c = VDescCall (VData dName vParams) (VSwitch vTuple vc)
                    vFuncTy = VExt vDesc_c vDatatype
                in VPi "p" vFuncTy $ \vFunc ->

                     let vIhTy = VSquare vDesc_c (VDecode VOmega . vApp vP) vFunc
                         vTargetExp = VDecode VOmega (vApp vP (VIn (VDPair "c" vc vFunc)))
                     in VPi "ih" vIhTy $ const vTargetExp

              vMTy = VSmallPiE vTagTm (VLam "c" (VCode VOmega . mBody))

          in VPi "m" vMTy $ \vM ->
               VPi "x" vDatatype $ \vX ->
                 VDecode VOmega (vApp vP vX)

      elimTyBodyTm = quoteTy (Lvl l_p) vElimTyBody

  in foldr (\((pName, _), pTyTm) acc -> Pi pName pTyTm acc) elimTyBodyTm (zip params pTyTms)

-- Elaborates the eliminator term
elabElimTm params (Lvl l_p) vDescSum =
  let
      vElimTmBody =
        VLam "P" $ \vP ->
        VLam "m" $ \vM ->
        VLam "x" $ \vX ->
          let vM_tm = VLam "y" $ \vY ->
                      VLam "ihs" $ \vIhs ->
                      vApp (vApp (VSwitch vM (VFst vY)) (VSnd vY)) vIhs
          in VElim vDescSum vP vM_tm vX
      elimTmBodyTm = quoteTm (Lvl l_p) vElimTmBody

  in foldr (\(pName, _) acc -> Lam pName acc) elimTmBodyTm params



infer :: Cxt -> Raw -> M (Tm, VTy)
infer cxt = \case
  RSrcPos pos t -> infer (cxt {pos = pos}) t

  RVar x -> do
    let go i [] = report cxt ("variable out of scope: " ++ x)
        go i ((x', a):tys)
          | x == x'   = case env cxt !! i of
                          VETm _ -> pure (Var (Ix i), a)
                          VESize _ -> report cxt ("Expected a term variable, but '" ++ x ++ "' is a level variable.")
          | otherwise = go (i + 1) tys
    go 0 (types cxt)

  RProj t x -> do
    (tTm, tTy) <- infer cxt t
    let elabProj c ty tm field = case ty of
          VSigma y a b ->
            if field == y then
              pure (Fst tm, a)
            else do
              let vFst = evalTm (env c) (Fst tm)
              elabProj c (b vFst) (Snd tm) field
          _ -> report c ("Field " ++ field ++ " not found in record")
    elabProj cxt tTy tTm x

  RRecord fields -> do
    ty <- checkTy cxt (RRecord fields) Omega
    pure (Code Omega ty, VU VOmega)

  RRecordVal [] -> pure (One, VUnit)
  RRecordVal _  -> report cxt "Cannot infer type of non-empty record value"

  RApp t u -> do
    (t', tty) <- infer cxt t
    case tty of
      VPi _ a b -> do
        u' <- check cxt u a
        pure (App t' u', b (evalTm (env cxt) u'))
      tty ->
        report cxt $ "Expected a function type, instead inferred:\n\n  " ++ showVTy cxt tty

  RLApp t s -> do
    (tTm, tTy) <- infer cxt t
    case tTy of
      VLPi _ b -> do
        sz <- elabSize cxt s
        let vsz = evalSize (env cxt) sz
        pure (LApp tTm sz, b vsz)
      _ -> report cxt ("Expected a level-polymorphic type for level application, instead inferred:\n\n  " ++ showVTy cxt tTy)

  RFst t -> do
    (tTm, tTy) <- infer cxt t
    case tTy of
      VSigma _ a _ -> pure (Fst tTm, a)
      VTensor a _  -> pure (Fst tTm, a)
      _ -> report cxt "Expected a pair for fst"

  RSnd t -> do
    (tTm, tTy) <- infer cxt t
    case tTy of
      VSigma _ _ b -> pure (Snd tTm, b (applyFst (evalTm (env cxt) tTm)))
      VTensor _ b  -> pure (Snd tTm, b)
      _ -> report cxt "Expected a pair for snd"

  RLet x aTm tTm uTm -> do
    aTm' <- checkTy cxt aTm Omega
    let ~va = evalTy (env cxt) aTm'
    tTm' <- check cxt tTm va
    let ~vt = evalTm (env cxt) tTm'
    (uTm', uty) <- infer (define x vt va cxt) uTm
    pure (Let x aTm' tTm' uTm', uty)

  ROne -> pure (One, VUnit)

  RData x params ty constrs u -> do
    -- First premise of rule (a) : elaborate the big Pi of parameters
    (tyParams, vTyParams, uLevel) <- elabDataTy cxt params ty

    -- Binding the Pi of parameters : in the second premise of rule (a)
    (cxt_params, pTyTms) <- buildParamCxt cxt params

    let constrsList = NE.toList constrs
    let tagTm = elabTags constrsList
    let tagTy = EnumT tagTm
    let vTagTy = evalTy (env cxt_params) tagTy
    let cxt_with_c = bind "c" vTagTy cxt_params

    -- Elaborate the list of descriptions corresponding to the type of each constructor
    desc_list <- forM constrsList $ \(_, cTyRaw) ->
                     elabConstrDesc x cxt_with_c cTyRaw

    -- Bundles the previous list in a single description corresponding to the datatype
    let n = length params
    let tuple = foldr (Pair . DReturn) One desc_list
    let descSum = elabFullDesc x n tagTy tuple

    -- Take the initial algebra of this description, and bundle it in a label type
    let muTy = Mu descSum
    let paramVars = [Var (Ix i) | i <- [n - 1, n - 2 .. 0]]
    let dLabelTy = DLabel (Data x paramVars) muTy

    -- We take the code of this type and put in in a lambda to get the conclusion of rule (a)
    let dCode = Code uLevel dLabelTy
    let term_D = foldr (\(p, _) acc -> Lam p acc) dCode params

    -- We add it to the context !
    let tags = iterate SuccE ZeroE
    let vTermD = evalTm (env cxt) term_D
    let cxt_initial_constrs = define x vTermD vTyParams cxt

    (cxt_with_constrs, wrapLets, constrsData) <- elabConstrs x params cxt_initial_constrs (zip constrsList tags)

    -- Eliminators 
    let vTuple = evalTm (env cxt_with_c) tuple
    let vTagTm = evalTm (env cxt_params) tagTm
    let vDescSum = evalDesc (env cxt_params) descSum

    let vuLevel = evalSize (env cxt_params) uLevel
    let elimTyFull = elabElimTy vuLevel x params pTyTms (lvl cxt_params) vTuple vTagTm vTermD
    let elimTmFull = elabElimTm params (lvl cxt_params) vDescSum

    let vElimTy = evalTy (env cxt) elimTyFull
    let vElimTm = evalTm (env cxt) elimTmFull

    let elimName = "elim" ++ x
    let cxt_final = define elimName vElimTm vElimTy cxt_with_constrs

    (uTm, uTy) <- infer cxt_final u

    let nfElimTy = quoteTy (lvl cxt_with_constrs) vElimTy
    let nfElimTm = quoteTm (lvl cxt_with_constrs) vElimTm

    let finalTm = Let x tyParams term_D $
                  wrapLets $
                  Let elimName nfElimTy nfElimTm uTm
    pure (finalTm, uTy)

  RPair {} -> report cxt "Can't infer type for Pair"
  RU {} -> report cxt "Can't infer type for universe"
  RPi {} -> report cxt "Can't infer type for product type"
  RLam {} -> report cxt "Can't infer type for lambda expression."
  RLPi {} -> report cxt "Can't infer type for level product type"
  RLAbs {} -> report cxt "Can't infer type for level abstraction"