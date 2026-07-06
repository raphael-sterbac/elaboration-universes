module Evaluation where

import Prelude hiding (lookup)

import Syntax

-- values
------------------------------------------------------------

data VEnvVal = VETm VTm | VESize VSize
type Env = [VEnvVal]
data VLabel = VData Name [VTm]

data VSize = VLVar Lvl | VZero | VSucc VSize | VBig | VOmega 

instance Eq VSize where
  VZero == VZero = True
  VBig == VBig = True
  VOmega == VOmega = True
  VLVar x == VLVar y = x == y
  VSucc s1 == VSucc s2 = s1 == s2
  _ == _ = False

instance Ord VSize where
  _ <= VOmega = True
  VOmega <= _ = False
  _ <= VBig = True
  VBig <= _ = False
  VZero <= _ = True
  VSucc s1 <= VSucc s2 = s1 <= s2
  VLVar x <= VLVar y = x == y
  VLVar x <= VSucc s2 = VLVar x <= s2
  _ <= _ = False
  
  VOmega < _ = False
  _ < VOmega = True
  VBig < _ = False
  _ < VBig = True
  VZero < VSucc _ = True
  VSucc s1 < VSucc s2 = s1 < s2
  VLVar x < VSucc s2 = VLVar x <= s2
  _ < _ = False

instance Show VSize where
  show (VLVar i) = show i
  show VZero = "0"
  show (VSucc s) = show s ++ " + 1"
  show VBig    = "Big"
  show VOmega  = "Omega"

data VTy
  = VPi Name ~VTy (VTm -> VTy)
  | VU VSize 
  | VDecode VSize VTm
  | VSigma Name VTy (VTm -> VTy)
  | VUnit
  | VLPi Name (VSize -> VTy)
  -- Descriptions
  | VTensor VTy VTy
  | VSquare VDesc (VTm -> VTy) VTm
  | VMu Env VDesc
  | VDLabel VLabel VTy
  | VExt VDesc VTy
  -- Enumerations
  | VEnumU
  | VEnumT VTm
  | VSmallPiE VTm VTm
    
data VTm
  = VVar Lvl
  | VApp VTm ~VTm
  | VCode VSize VTy
  | VLam Name (VTm -> VTm)
  | VPair VTm VTm
  | VDPair Name VTm VTm
  | VFst VTm
  | VSnd VTm
  | VOne
  | VConLabel Name VTm
  | VLAbs Name (VSize -> VTm)
  | VLApp VTm VSize
  -- Descriptions
  | VIn VTm
  | VSquareMap VDesc VTm VTm
  | VExtMap VDesc VTm VTm
  | VElim VDesc VTm VTm VTm
  | VDReturn VDesc
  -- Enumerations
  | VNilE
  | VConsE Name VTm
  | VZeroE 
  | VSuccE VTm
  | VSwitch VTm VTm

data VDesc
  = VDescUnit
  | VDescVar
  | VDescTensor VDesc VDesc
  | VDescSum Name VTy (VTm -> VDesc)
  | VDescProd Name VTy (VTm -> VDesc)
  | VDescCall VLabel VTm

--------------------------------------------------------------------------------

-- evaluation algorithm
------------------------------------------------------------

vApp :: VTm -> VTm -> VTm
vApp (VLam _ f) v = f v
vApp f          v = VApp f v

vLApp :: VTm -> VSize -> VTm
vLApp (VLAbs _ f) s = f s
vLApp f           s = VLApp f s

-- External functions for descriptions
applyExtMap :: VDesc -> VTm -> VTm -> VTm
applyExtMap d vf vm = case d of
  VDescUnit -> VOne
  VDescVar -> vApp vf vm
  VDescTensor e1 e2 -> VPair (applyExtMap e1 vf (applyFst vm)) (applyExtMap e2 vf (applySnd vm))
  VDescSum n a d1 -> VDPair n (applyFst vm) (applyExtMap (d1 (applyFst vm)) vf (applySnd vm))
  VDescProd n a d1 -> VLam n \v -> applyExtMap (d1 v) vf (vApp vm v)
  VDescCall l k -> VExtMap d vf vm

applySquareMap :: VDesc -> VTm -> VTm -> VTm
applySquareMap d vf vm = case d of
  VDescUnit -> VOne
  VDescVar -> vApp vf vm
  VDescTensor d1 d2 -> VPair (applySquareMap d1 vf (applyFst vm)) (applySquareMap d2 vf (applySnd vm))
  VDescSum n a d1 -> applySquareMap (d1 (applyFst vm)) vf (applySnd vm)
  VDescProd n a d1 -> VLam n \v -> applySquareMap (d1 v) vf (vApp vm v)
  VDescCall l k -> VSquareMap d vf vm

applySwitch :: VTm -> VTm -> VTm
applySwitch vt vu = case vu of
  VZeroE -> applyFst vt
  VSuccE x -> applySwitch (applySnd vt) x
  k -> VSwitch vt k

applyElim :: VDesc -> VTm -> VTm -> VTm -> VTm
applyElim d vc vm vn = 
  let strip (VConLabel _ t) = strip t
      strip t = t
  in case strip vn of
    VIn x -> 
      let recElim = VLam "_" \v -> applyElim d vc vm v
          ihs = applySquareMap d recElim x
      in vApp (vApp vm x) ihs
    _ -> VElim d vc vm vn

applyFst :: VTm -> VTm
applyFst (VPair t _) = t
applyFst (VDPair _ t _) = t
applyFst v = VFst v

applySnd :: VTm -> VTm
applySnd (VPair _ u) = u
applySnd (VDPair _ _ u) = u
applySnd v = VSnd v

evalSize :: Env -> Size -> VSize
evalSize env = \case
  LVar (Ix x) -> case env !! x of
    VESize s -> s
    _ -> error "Evaluation error: Expected a level variable in environment"
  Zero -> VZero 
  Succ s -> VSucc (evalSize env s)
  Big -> VBig
  Omega -> VOmega

evalTm :: Env -> Tm -> VTm
evalTm env = \case
  Var (Ix x) -> case env !! x of
    VETm t -> t
    _ -> error "Evaluation error: Expected a term variable in environment"
  App t u -> vApp (evalTm env t) (evalTm env u)
  Lam x t -> VLam x \v -> evalTm (VETm v : env) t
  Let x _ t u -> evalTm (VETm (evalTm env t) : env) u
  Pair t u -> VPair (evalTm env t) (evalTm env u)
  DPair x t u -> VDPair x (evalTm env t) (evalTm env u)
  One -> VOne
  In t -> VIn (evalTm env t)
  Fst t -> applyFst (evalTm env t)
  Snd t -> applySnd (evalTm env t)
  ConLabel n t -> VConLabel n (evalTm env t)

  LAbs x t -> VLAbs x \i -> evalTm (VESize i : env) t
  LApp t s -> vLApp (evalTm env t) (evalSize env s)
  
  -- Case of a Coding
  Code s a      -> VCode (evalSize env s) (evalTy env a)
  
  -- Descriptions
  ExtMap d f m -> 
    let vf = evalTm env f
        vm = evalTm env m
        vd = evalDesc env d
    in applyExtMap vd vf vm
    
  SquareMap d f m -> 
    let vf = evalTm env f
        vm = evalTm env m
        vd = evalDesc env d
    in applySquareMap vd vf vm

  Elim d c m n ->
    let vc = evalTm env c
        vm = evalTm env m
        vn = evalTm env n
        vd = evalDesc env d
    in applyElim vd vc vm vn

  DReturn d -> VDReturn (evalDesc env d)

  -- Enumerations
  NilE       -> VNilE
  ConsE n t  -> VConsE n (evalTm env t)
  ZeroE      -> VZeroE
  SuccE t    -> VSuccE (evalTm env t)
  Switch t u -> 
    let vt = evalTm env t
        vu = evalTm env u
    in applySwitch vt vu

applyExt :: VDesc -> VTy -> VTy
applyExt vd vx = case vd of
  VDescUnit -> VUnit
  VDescVar -> vx
  VDescTensor d1 d2 -> VTensor (applyExt d1 vx) (applyExt d2 vx)
  VDescSum n a d1 -> VSigma n a \v -> applyExt (d1 v) vx
  VDescProd n a d1 -> VPi n a \v -> applyExt (d1 v) vx
  VDescCall l k -> VExt vd vx

applySquare :: VDesc -> (VTm -> VTy) -> VTm -> VTy
applySquare vd p vm = case vd of
  VDescUnit -> VUnit 
  VDescVar -> p vm
  VDescTensor d e -> VTensor (applySquare d p (applyFst vm)) (applySquare e p (applySnd vm))
  VDescSum n a d1 -> applySquare (d1 (applyFst vm)) p (applySnd vm)
  VDescProd n a d1 -> VPi n a \v -> applySquare (d1 v) p (vApp vm v)
  VDescCall l k -> VSquare vd p vm

evalTy :: Env -> Ty -> VTy
evalTy env = \case
  Pi x a b -> VPi x (evalTy env a) \v -> evalTy (VETm v : env) b
  U s -> VU (evalSize env s)
  Sigma x a b -> VSigma x (evalTy env a) \v -> evalTy (VETm v : env) b
  Tensor a b -> VTensor (evalTy env a) (evalTy env b)
  Unit -> VUnit
  DLabel (Data n ts) ty -> VDLabel (VData n (map (evalTm env) ts)) (evalTy env ty)

  -- Case of a Decoding
  Decode i t -> case evalTm env t of
    VCode j a | (evalSize env i) == j -> a
    v                   -> VDecode (evalSize env i) v

  LPi x t -> VLPi x \i -> evalTy (VESize i : env) t

  -- Descriptions
  Ext d x -> 
    let vd = evalDesc env d
        vx = evalTy env x
    in applyExt vd vx

  Square d p m ->
    let vp = \v -> evalTy ((VETm v):env) p
        vm = evalTm env m
        vd = evalDesc env d
    in applySquare vd vp vm
  Mu d -> VMu env (evalDesc env d)
  
  -- Enumerations
  EnumU -> VEnumU
  EnumT t -> VEnumT (evalTm env t)
  SmallPiE t u -> VSmallPiE (evalTm env t) (evalTm env u)

evalDesc :: Env -> Desc -> VDesc
evalDesc env = \case
  DescUnit -> VDescUnit
  DescVar -> VDescVar
  DescTensor d1 d2 -> VDescTensor (evalDesc env d1) (evalDesc env d2)
  DescSum n a d -> VDescSum n (evalTy env a) \v -> evalDesc (VETm v : env) d
  DescProd n a d -> VDescProd n (evalTy env a) \v -> evalDesc (VETm v : env) d
  DescCall (Data n ts) t -> case (evalTm env t) of
    VDReturn d -> d
    k -> VDescCall (VData n (map (evalTm env) ts)) k

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quoteSize :: Lvl -> VSize -> Size
quoteSize l = \case
  VLVar x -> LVar (lvl2Ix l x)
  VZero -> Zero
  VSucc s -> Succ (quoteSize l s)
  VBig -> Big
  VOmega -> Omega
quoteTm :: Lvl -> VTm -> Tm
quoteTm l = \case
  VVar x -> Var (lvl2Ix l x)
  VApp t u -> App (quoteTm l t) (quoteTm l u)
  VLam x t -> Lam x (quoteTm (l + 1) (t (VVar l)))
  VPair t u -> Pair (quoteTm l t) (quoteTm l u)
  VDPair x t u -> DPair x (quoteTm l t) (quoteTm l u)
  VOne -> One
  VFst t -> Fst (quoteTm l t)
  VSnd t -> Snd (quoteTm l t)
  VConLabel n t -> ConLabel n (quoteTm l t)

  VLAbs x t -> LAbs x (quoteTm (l+1) (t (VLVar l)))
  VLApp t s -> LApp (quoteTm l t) (quoteSize l s)

  -- Case of a Coding
  VCode s a   -> Code (quoteSize l s) (quoteTy l a)

  -- Descriptions
  VIn t -> In (quoteTm l t)
  VSquareMap d f m -> SquareMap (quoteDesc l d) (quoteTm l f) (quoteTm l m)
  VExtMap d f m -> ExtMap (quoteDesc l d) (quoteTm l f) (quoteTm l m)
  VElim d c m n -> Elim (quoteDesc l d) (quoteTm l c) (quoteTm l m) (quoteTm l n)
  VDReturn d -> DReturn (quoteDesc l d)

  -- Enumerations
  VNilE -> NilE
  VConsE n t -> ConsE n (quoteTm l t)
  VZeroE -> ZeroE
  VSuccE t -> SuccE (quoteTm l t)
  VSwitch t u -> Switch (quoteTm l t) (quoteTm l u)

quoteTy :: Lvl -> VTy -> Ty
quoteTy l = \case
  VPi  x a b  -> Pi x (quoteTy l a) (quoteTy (l + 1) (b (VVar l)))
  VU s -> U (quoteSize l s)
  VSigma x a b -> Sigma x (quoteTy l a) (quoteTy (l + 1) (b (VVar l)))
  VUnit -> Unit
  VTensor a b -> Tensor (quoteTy l a) (quoteTy l b)
  VDLabel (VData n ts) ty -> DLabel (Data n (map (quoteTm l) ts)) (quoteTy l ty)
  VLPi x t -> LPi x (quoteTy (l+1) (t (VLVar l)))
  
  -- Case of a Decoding
  VDecode s t -> Decode (quoteSize l s) (quoteTm l t)

  -- Descriptions
  VSquare d p m -> Square (quoteDesc l d) (quoteTy (l + 1) (p (VVar l))) (quoteTm l m)
  VMu _ d -> Mu (quoteDesc l d)
  VExt d x -> Ext (quoteDesc l d) (quoteTy l x)

  -- Enumerations
  VEnumU -> EnumU
  VEnumT t -> EnumT (quoteTm l t)
  VSmallPiE t u -> SmallPiE (quoteTm l t) (quoteTm l u)

quoteDesc :: Lvl -> VDesc -> Desc
quoteDesc l = \case
  VDescUnit -> DescUnit
  VDescVar -> DescVar
  VDescTensor d1 d2 -> DescTensor (quoteDesc l d1) (quoteDesc l d2)
  VDescSum n a d -> DescSum n (quoteTy l a) (quoteDesc (l + 1) (d (VVar l)))
  VDescProd n a d -> DescProd n (quoteTy l a) (quoteDesc (l + 1) (d (VVar l)))
  VDescCall (VData n ts) t -> DescCall (Data n (map (quoteTm l) ts)) (quoteTm l t)

nf :: Env -> Tm -> Tm
nf env t = quoteTm (Lvl (length env)) (evalTm env t)