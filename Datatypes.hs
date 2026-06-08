module Main where

import Prelude hiding (lookup)
import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Void
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import System.Environment (getArgs)
import System.Exit
import Text.Megaparsec
import Text.Printf

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

-- syntax
--------------------------------------------------------------------------------

-- De Bruijn index.
newtype Ix  = Ix  Int deriving (Eq, Show, Num) via Int

-- De Bruijn level.
newtype Lvl = Lvl Int deriving (Eq, Show, Num) via Int

data Size = Sz Int | Big | Omega deriving (Eq)

instance Ord Size where
  Sz i <= Sz j = i <= j
  Sz _ <= Big = True
  Sz _ <= Omega = True
  Big <= Big = True
  Big <= Omega = True
  Omega <= Omega = True
  _ <= _ = False

  Sz i < Sz j = i < j
  Sz _ < Big = True
  Sz _ < Omega = True
  Big < Omega = True
  _ < _ = False

instance Show Size where
  show (Sz i) = show i
  show Big    = "Tp"
  show Omega  = "Omega"

type Name = String

data Raw
  = RVar Name
  | RLam Name Raw
  | RApp Raw Raw
  | RU Size
  | RPi Name Raw Raw
  | RPair Raw Raw
  | ROne
  | RAt Raw Size
  | RFst Raw
  | RSnd Raw
  | RLet Name Raw Raw Raw
  | RSrcPos SourcePos Raw
  | RData Name [(Name, Raw)] Raw (NonEmpty (Name, Raw)) Raw
  deriving Show

-- core syntax
------------------------------------------------------------

data Label 
  = Data Name [Tm]

data Desc
  = DescUnit
  | DescVar
  | DescTensor Desc Desc
  | DescSum Name Ty Desc
  | DescProd Name Ty Desc
  | DescCall Label Tm 

data Ty
  = Pi Name ~Ty Ty
  | U Size 
  | Decode Size Tm
  | Unit
  | Sigma Name ~Ty Ty
  | Tensor Ty Ty
  -- Descriptions
  | Ext Desc Ty
  | Mu Desc
  | Square Desc ~Ty Tm
  | DLabel Label Ty
  -- Enumerations
  | EnumU
  | EnumT Tm
  | SmallPiE Tm Tm

data Tm
  = Var Ix
  | App Tm ~Tm
  | Code Size Ty
  | Lam Name Tm
  | Let Name Ty Tm Tm
  | Pair Tm Tm
  | DPair Name Tm Tm
  | Fst Tm
  | Snd Tm
  | One
  | ConLabel Name Tm
  -- Descriptions 
  | In Tm
  | SquareMap Desc Tm Tm
  | ExtMap Desc Tm Tm
  | Elim Desc Tm Tm Tm
  | DReturn Desc
  -- Enumerations
  | NilE
  | ConsE Name Tm
  | ZeroE 
  | SuccE Tm
  | Switch Tm Tm

-- values
------------------------------------------------------------

type Env = [VTm]
data VLabel = VData Name [VTm]

data VTy
  = VPi Name ~VTy (VTm -> VTy)
  | VU Size 
  | VDecode Size VTm
  | VSigma Name VTy (VTm -> VTy)
  | VUnit
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
  | VCode Size VTy
  | VLam Name (VTm -> VTm)
  | VPair VTm VTm
  | VDPair Name VTm VTm
  | VFst VTm
  | VSnd VTm
  | VOne
  | VConLabel Name VTm
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

vApp :: VTm -> VTm -> VTm
vApp (VLam _ f) v = f v
vApp f          v = VApp f v

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

evalTm :: Env -> Tm -> VTm
evalTm env = \case
  Var (Ix x)    -> env !! x
  App t u       -> vApp (evalTm env t) (evalTm env u)
  Lam x t       -> VLam x \v -> evalTm (v:env) t
  Let x _ t u   -> evalTm (evalTm env t : env) u
  Pair t u      -> VPair (evalTm env t) (evalTm env u)
  DPair x t u   -> VDPair x (evalTm env t) (evalTm env u)
  One           -> VOne
  In t          -> VIn (evalTm env t)
  Fst t         -> applyFst (evalTm env t)
  Snd t         -> applySnd (evalTm env t)
  ConLabel n t  -> VConLabel n (evalTm env t)
  
  -- Case of a Coding
  Code s a      -> VCode s (evalTy env a)
  
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
  Pi x a b      -> VPi x (evalTy env a) \v -> evalTy (v:env) b
  U s           -> VU s
  Sigma x a b   -> VSigma x (evalTy env a) \v -> evalTy (v:env) b
  Tensor a b    -> VTensor (evalTy env a) (evalTy env b)
  Unit          -> VUnit
  DLabel (Data n ts) ty -> VDLabel (VData n (map (evalTm env) ts)) (evalTy env ty)

  -- Case of a Decoding
  Decode i t    -> case evalTm env t of
    VCode j a | i == j  -> a
    v                   -> VDecode i v

  -- Descriptions
  Ext d x -> 
    let vd = evalDesc env d
        vx = evalTy env x
    in applyExt vd vx

  Square d p m ->
    let vp = \v -> evalTy (v:env) p
        vm = evalTm env m
        vd = evalDesc env d
    in applySquare vd vp vm
  Mu d -> VMu env (evalDesc env d)
  
  -- Enumerations
  EnumU        -> VEnumU
  EnumT t      -> VEnumT (evalTm env t)
  SmallPiE t u -> VSmallPiE (evalTm env t) (evalTm env u)

evalDesc :: Env -> Desc -> VDesc
evalDesc env = \case
  DescUnit         -> VDescUnit
  DescVar          -> VDescVar
  DescTensor d1 d2 -> VDescTensor (evalDesc env d1) (evalDesc env d2)
  DescSum n a d    -> VDescSum n (evalTy env a) \v -> evalDesc (v:env) d
  DescProd n a d   -> VDescProd n (evalTy env a) \v -> evalDesc (v:env) d
  DescCall (Data n ts) t -> case (evalTm env t) of
    VDReturn d -> d
    k -> VDescCall (VData n (map (evalTm env) ts)) k

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quoteTm :: Lvl -> VTm -> Tm
quoteTm l = \case
  VVar x      -> Var (lvl2Ix l x)
  VApp t u    -> App (quoteTm l t) (quoteTm l u)
  VLam x t    -> Lam x (quoteTm (l + 1) (t (VVar l)))
  VPair t u   -> Pair (quoteTm l t) (quoteTm l u)
  VDPair x t u -> DPair x (quoteTm l t) (quoteTm l u)
  VOne -> One
  VFst t -> Fst (quoteTm l t)
  VSnd t -> Snd (quoteTm l t)
  VConLabel n t -> ConLabel n (quoteTm l t)

  -- Case of a Coding
  VCode s a   -> Code s (quoteTy l a)

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
  VU s        -> U s
  VSigma x a b -> Sigma x (quoteTy l a) (quoteTy (l + 1) (b (VVar l)))
  VUnit       -> Unit
  VTensor a b -> Tensor (quoteTy l a) (quoteTy l b)
  VDLabel (VData n ts) ty -> DLabel (Data n (map (quoteTm l) ts)) (quoteTy l ty)
  
  -- Case of a Decoding
  VDecode s t -> Decode s (quoteTm l t)

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

convTm :: Lvl -> VTm -> VTm -> Bool
convTm l t u =
  let strip (VConLabel _ tm) = strip tm
      strip tm = tm
  in case (strip t, strip u) of
  (VLam _ t, VLam _ t') -> convTm (l + 1) (t (VVar l)) (t' (VVar l))

  (VLam _ t, u) -> convTm (l + 1) (t (VVar l)) (VApp u (VVar l))
  (u, VLam _ t) -> convTm (l + 1) (VApp u (VVar l)) (t (VVar l))

  (VVar x  , VVar x'   ) -> x == x'
  (VApp t u, VApp t' u') -> convTm l t t' && convTm l u u'

  (VPair t1 u1, VPair t2 u2) -> convTm l t1 t2 && convTm l u1 u2
  (VDPair _ t1 u1, VDPair _ t2 u2) -> convTm l t1 t2 && convTm l u1 u2
  (VOne, VOne) -> True
  (VFst t, VFst u) -> convTm l t u
  (VSnd t, VSnd u) -> convTm l t u

  (VCode s a, VCode s' b) | s == s' -> convTy l a b

  -- Descriptions
  (VIn t1, VIn t2) -> convTm l t1 t2
  (VSquareMap d f m, VSquareMap d' f' m') -> convDesc l d d' && convTm l f f' && convTm l m m'
  (VExtMap d f m, VExtMap d' f' m') -> convDesc l d d' && convTm l f f' && convTm l m m'
  (VElim d c m n, VElim d' c' m' n') -> convDesc l d d' && convTm l c c' && convTm l m m' && convTm l n n'
  (VDReturn d, VDReturn d') -> convDesc l d d'

  -- Enumerations
  (VNilE, VNilE) -> True
  (VConsE _ t, VConsE _ t') -> convTm l t t'
  (VZeroE, VZeroE) -> True
  (VSuccE t, VSuccE t') -> convTm l t t'
  (VSwitch t u, VSwitch t' u') -> convTm l t t' && convTm l u u'

  _ -> False

convTy :: Lvl -> VTy -> VTy -> Bool
convTy l t u =
  let strip (VDLabel _ ty) = strip ty
      strip ty = ty
  in case (strip t, strip u) of
  (VU s, VU s') -> s == s'
  (VUnit, VUnit) -> True
  (VTensor a b, VTensor a' b') -> convTy l a a' && convTy l b b'

  (VPi _ a b, VPi _ a' b') -> convTy l a a' && convTy (l + 1) (b (VVar l)) (b' (VVar l))
  (VSigma _ a b, VSigma _ a' b') -> convTy l a a' && convTy (l + 1) (b (VVar l)) (b' (VVar l))
  (VDecode i a, VDecode j b) | i == j -> convTm l a b

  -- Descriptions
  (VSquare d p m, VSquare d' p' m') -> convDesc l d d'  && convTy (l + 1) (p (VVar l)) (p' (VVar l))  && convTm l m m'
  (VMu _ d, VMu _ d') -> convDesc l d d'
  (VExt d x, VExt d' x') -> convDesc l d d' && convTy l x x'

  -- Enumerations
  (VEnumU, VEnumU) -> True
  (VEnumT t, VEnumT t') -> convTm l t t'
  (VSmallPiE t u, VSmallPiE t' u') -> convTm l t t' && convTm l u u'

  _ -> False

convDesc :: Lvl -> VDesc -> VDesc -> Bool
convDesc l d d' = case (d, d') of
  (VDescUnit, VDescUnit) -> True
  (VDescVar, VDescVar) -> True
  (VDescTensor a b, VDescTensor a' b') -> convDesc l a a' && convDesc l b b'
  (VDescSum _ a b, VDescSum _ a' b') -> convTy l a a' && convDesc (l + 1) (b (VVar l)) (b' (VVar l))
  (VDescProd _ a b, VDescProd _ a' b') -> convTy l a a' && convDesc (l + 1) (b (VVar l)) (b' (VVar l))
  (VDescCall (VData n ts) t, VDescCall (VData n' ts') t') -> 
      n == n' && length ts == length ts' && and (zipWith (convTm l) ts ts') && convTm l t t'
  _ -> False

-- Elaboration
--------------------------------------------------------------------------------

type Types = [(Name, VTy)]

data Cxt = Cxt {env :: Env, types :: Types, lvl :: Lvl, pos :: SourcePos}

emptyCxt :: SourcePos -> Cxt
emptyCxt = Cxt [] [] 0

bind :: Name -> VTy -> Cxt -> Cxt
bind x ~a (Cxt env types l pos) =
  Cxt (VVar l:env) ((x, a):types) (l + 1) pos

define :: Name -> VTm -> VTy -> Cxt -> Cxt
define x ~t ~a (Cxt env types l pos) =
  Cxt (t:env) ((x, a):types) (l + 1) pos

type M = Either (String, SourcePos)

report :: Cxt -> String -> M a
report cxt msg = Left (msg, pos cxt)

deriving instance Show Tm
deriving instance Show Ty
deriving instance Show Label
deriving instance Show Desc

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
    VU i -> pure (t', i)
    _    -> report cxt "expected a type"
    
isSmall :: Cxt -> Size -> VTy -> M ()
isSmall cxt i = \case
  VU j | j < i -> pure ()
  VU j -> report cxt ("Universe " ++ show j ++ " is not small at level " ++ show i)
  VDecode j _ | j <= i -> pure ()
  VDecode j _ -> report cxt ("Decoded type at level " ++ show j ++ " is not small at level " ++ show i)
  
  VPi _ a b -> do
      isSmall cxt i a
      isSmall cxt i (b (VVar (lvl cxt)))
      

  -- TODO : This is a bit weird, shouldn't we "evaluate" in evalTy ?
  VSigma _ a b -> case a of
      VEnumT tags -> do
          let checkBranches t idx = case t of
                VNilE -> pure ()
                VConsE _ rest -> do
                    isSmall cxt i (b idx)
                    checkBranches rest (VSuccE idx)
                _ -> report cxt "Cannot prove smallness: opaque enumeration tags"
          checkBranches tags VZeroE
      _ -> do
          isSmall cxt i a
          isSmall cxt i (b (VVar (lvl cxt)))
          
  VTensor a b -> do
      isSmall cxt i a
      isSmall cxt i b
  VUnit -> pure ()
  VDLabel _ ty -> isSmall cxt i ty
  
  VMu _ d -> do
      let l = lvl cxt
      let cxt' = bind "_" (VU i) cxt
      isSmall cxt' i (applyExt d (VDecode i (VVar l)))
      
  VEnumU -> pure ()
  VEnumT _ -> pure ()
  VSmallPiE _ _ -> pure () 

  VExt _ _ -> report cxt "Cannot prove smallness: opaque description extension"
  VSquare _ _ _ -> report cxt "Cannot prove smallness: opaque square"

coe :: Cxt -> Lvl -> VTy -> VTy -> Tm -> M Tm
coe cxt l sourceTy targetTy m = case (sourceTy, targetTy) of
  (VU i, VU j) | i <= j -> 
    pure $ Code j (Decode i m)

  (VPi n1 a1 b1, VPi n2 a2 b2) -> do
    let cxt' = bind n2 a2 cxt
    let l' = lvl cxt'
    
    u_x <- coe cxt' l' a2 a1 (Var (Ix 0))

    let env' = env cxt'
    let vu_x = evalTm env' u_x
    let vm = evalTm (env cxt) m
    let vApp' = case vm of
                VLam _ f -> f vu_x
                _        -> VApp vm vu_x
    let m_u_x = quoteTm l' vApp'
    
    n_x <- coe cxt' l' (b1 vu_x) (b2 (VVar l)) m_u_x
    
    pure $ Lam n2 n_x

  _ -> 
    if convTy l sourceTy targetTy then
      pure m 
    else report cxt ("Error: Invalid coercion " ++ showVTy cxt sourceTy ++ "\n \n to \n \n" ++ showVTy cxt targetTy)

checkTy :: Cxt -> Raw -> Size -> M Ty
checkTy cxt t size = case t of
  RSrcPos pos t -> checkTy (cxt {pos = pos}) t size

  RU s' -> 
    if s' < size 
    then pure $ U s'
    else report cxt ("Size issue: U " ++ show s' ++ " is too large to fit in " ++ show size)

  RAt t s' -> 
    if s' > size 
    then report cxt ("Size annotation @" ++ show s' ++ " is too large for expected size " ++ show size)
    else checkTy cxt t s'

  RPi x a b -> do
    a' <- checkTy cxt a size
    let cxt' = bind x (evalTy (env cxt) a') cxt
    b' <- checkTy cxt' b size
    pure $ Pi x a' b'

  _ -> do 
    (tTm, aTy) <- infer cxt t
    case aTy of
      VU s' -> 
        if s' <= size 
        then pure (Decode s' tTm)
        else do
            let ty = Decode s' tTm
            isSmall cxt size (evalTy (env cxt) ty)
            pure ty
        
      _ -> report cxt "Elaboration error: Expected a code"
    
check :: Cxt -> Raw -> VTy -> M Tm
check cxt t a = case (t, a) of
  (RSrcPos pos t, a) -> check (cxt {pos = pos}) t a

  (RLam x t, VPi x' a b) ->
    Lam x <$> check (bind x a cxt) t (b (VVar (lvl cxt)))

  (_, VU s) -> do
    u <- checkTy cxt t s
    pure $ Code s u

  (ROne, VUnit) -> pure One

  (ROne, VSmallPiE VNilE _) -> pure One

  (RPair t1 t2, VSmallPiE (VConsE _ eRest) f) -> do
      let getTy (VCode _ ty) = ty
          getTy v            = VDecode Big v 
          
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
    let ~va = evalTy (env cxt) aTm'
    tTm' <- check cxt tTm va
    let ~vt = evalTm (env cxt) tTm'
    uTm' <- check (define x vt va cxt) uTm a' 
    pure (Let x aTm' tTm' uTm')

  _ -> do
    (m, bTy) <- infer cxt t
    coe cxt (lvl cxt) bTy a m
    
isRec :: Name -> Raw -> Bool
isRec d (RSrcPos _ t) = isRec d t 
isRec d (RVar y) = y == d
isRec d (RApp f _) = isRec d f
isRec d _ = False


-- Function to handle "infinite" recursive definitions, like ex7
-- TODO : check this more carefuly
isInfRec :: Name -> Raw -> Bool
isInfRec d = \case
  RSrcPos _ t -> isInfRec d t
  RPi _ _ cod -> isRec d cod || isInfRec d cod
  _ -> False

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

-- Elaborates the type of the big Pi of the parameters, returns the type, its semantics and its size
elabDataTy :: Cxt -> [(Name, Raw)] -> Raw -> M (Ty, VTy, Size)
elabDataTy cxt params ty = do
  let tyD_raw = foldr (\(p, pTy) acc -> RPi p pTy acc) ty params
  tyD <- checkTy cxt tyD_raw Omega
  let vTyD = evalTy (env cxt) tyD

  let getSize (U s) = s
      getSize (Decode s _) = s
      getSize (Pi _ _ b) = getSize b
      getSize _ = Big
  pure (tyD, vTyD, getSize tyD)

-- Adds all the parameters in the context
buildParamCxt :: Cxt -> [(Name, Raw)] -> M (Cxt, [Ty])
buildParamCxt c [] = pure (c, [])
buildParamCxt c ((p, pTy):ps) = do
  pTyTm <- checkTy c pTy Omega
  let vpTy = evalTy (env c) pTyTm
  (c', pTyTms) <- buildParamCxt (bind p vpTy c) ps
  pure (c', pTyTm : pTyTms)

elabTags :: [(Name, Raw)] -> Tm
elabTags = foldr (\(cName, _) acc -> ConsE cName acc) NilE

-- Elaborates the description associated to a raw term (rule e)
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

-- Elaborates the full description with all the parameters, by calling elabConstrDesc
elabFullDesc :: Name -> Int -> Ty -> Tm -> Desc
elabFullDesc dName numParams tagTy tuple =
  let paramVars = [Var (Ix i) | i <- [numParams, numParams - 1 .. 1]]
      switchTm = Switch tuple (Var 0)
      descCall = DescCall (Data dName paramVars) switchTm
  in DescSum "c" tagTy descCall


-- Elaborate constructor
elabConstrTm :: Name -> Name -> [(Name, Raw)] -> Raw -> Tm -> Tm
elabConstrTm dName cName params cTyRaw cTag =
  let getArgs (RSrcPos _ t) = getArgs t
      getArgs (RPi y _ b) = y : getArgs b
      getArgs _ = []
      args = getArgs cTyRaw
      numArgs = length args
      
      -- Rule (d)
      elabArg (RSrcPos _ t) idx = elabArg t idx
      elabArg (RPi y a b) idx =
        if isRec dName a || isInfRec dName a then
          Pair (Var (Ix idx)) (elabArg b (idx - 1))
        else
          DPair y (Var (Ix idx)) (elabArg b (idx - 1))
      elabArg _ _ = One
      
      payload = elabArg cTyRaw (numArgs - 1)
      inner = ConLabel cName (In (DPair "c" cTag payload))
      body = foldr Lam inner args
  in foldr (\(p, _) acc -> Lam p acc) body params


-- Elaborates all the constructors
elabConstrs :: Name -> [(Name, Raw)] -> Cxt -> [((Name, Raw), Tm)] -> M (Cxt, Tm -> Tm, [(Name, Ty, Tm)])
elabConstrs dName params c [] = pure (c, id, [])
elabConstrs dName params c (((cName, cTyRaw), cTag) : rest) = do
  let fullTyRaw = foldr (\(p, pTy) acc -> RPi p pTy acc) cTyRaw params
  
  cTyTm <- checkTy c fullTyRaw Omega
  let term = elabConstrTm dName cName params cTyRaw cTag  

  let vcTy = evalTy (env c) cTyTm
  let vcTerm = evalTm (env c) term
  
  (cFinal, wrapLet, constrsData) <- elabConstrs dName params (define cName vcTerm vcTy c) rest
  
  pure (cFinal, \body -> Let cName cTyTm term (wrapLet body), (cName, cTyTm, term) : constrsData)

-- Elaborates the eliminator type
elabElimTy :: Size -> Name -> [(Name, Raw)] -> [Ty] -> Lvl -> VTm -> VTm -> VTm -> Ty
elabElimTy uLevel dName params pTyTms (Lvl l_p) vTuple vTagTm vTermD =
  let n = length params
      
      vParams = [VVar (Lvl i) | i <- [l_p - n .. l_p - 1]]
      vDatatypeCode = foldl vApp vTermD vParams      
      
      vDatatype = VDecode uLevel vDatatypeCode
      
      vPTy = VPi "x" vDatatype (\_ -> VU Omega)
      vTarget v = VDecode Omega v
      
      -- TODO : check the "hardcoded" eliminator type more carefuly
      -- I have put Omega to allow large elimination, should we ?
      vElimTyBody =
        VPi "P" vPTy $ \vP ->
          
          let mBody vc =
                let vDesc_c = VDescCall (VData dName vParams) (VSwitch vTuple vc)
                    vFuncTy = VExt vDesc_c vDatatype
                in VPi "p" vFuncTy $ \vFunc ->
                     
                     let vIhTy = VSquare vDesc_c (\vx -> vTarget (vApp vP vx)) vFunc
                         vTargetExp = vTarget (vApp vP (VIn (VDPair "c" vc vFunc)))
                     in VPi "ih" vIhTy $ \_ -> vTargetExp
              
              vMTy = VSmallPiE vTagTm (VLam "c" (\vc -> VCode Omega (mBody vc)))
          
          in VPi "m" vMTy $ \vM ->
               VPi "x" vDatatype $ \vX ->
                 vTarget (vApp vP vX)
                 
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
          | x == x'   = pure (Var i, a)
          | otherwise = go (i + 1) tys
    go 0 (types cxt)

  RApp t u -> do
    (t', tty) <- infer cxt t
    case tty of
      VPi _ a b -> do
        u' <- check cxt u a
        pure (App t' u', b (evalTm (env cxt) u'))
      tty ->
        report cxt $ "Expected a function type, instead inferred:\n\n  " ++ showVTy cxt tty

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

  RAt t s -> do
    ty <- checkTy cxt t s
    pure (Code s ty, VU s)

  ROne -> pure (One, VUnit)

  RData x params ty constrs u -> do
    (tyD, vTyD, uLevel) <- elabDataTy cxt params ty
    
    (cxt_params, pTyTms) <- buildParamCxt cxt params
    
    let constrsList = NE.toList constrs
    let tagTm = elabTags constrsList
    let tagTy = EnumT tagTm
    let vTagTy = evalTy (env cxt_params) tagTy
    let cxt_with_c = bind "c" vTagTy cxt_params
    
    desc_list <- forM constrsList $ \(_, cTyRaw) -> 
                     elabConstrDesc x cxt_with_c cTyRaw
                     
    let n = length params
    let tuple = foldr (\d acc -> Pair (DReturn d) acc) One desc_list
    let descSum = elabFullDesc x n tagTy tuple
    
    let muTy = Mu descSum 
    let paramVars = [Var (Ix i) | i <- [n - 1, n - 2 .. 0]]
    let dLabelTy = DLabel (Data x paramVars) muTy 
    
    let dCode = Code uLevel dLabelTy
    let term_D = foldr (\(p, _) acc -> Lam p acc) dCode params
    
    let tags = iterate SuccE ZeroE
    let vTermD = evalTm (env cxt) term_D
    let cxt_initial_constrs = define x vTermD vTyD cxt
    
    (cxt_with_constrs, wrapLets, constrsData) <- elabConstrs x params cxt_initial_constrs (zip constrsList tags)
    
    -- Eliminators 
    let vTuple = evalTm (env cxt_with_c) tuple
    let vTagTm = evalTm (env cxt_params) tagTm
    let vDescSum = evalDesc (env cxt_params) descSum
    
    let elimTyFull = elabElimTy uLevel x params pTyTms (lvl cxt_params) vTuple vTagTm vTermD
    let elimTmFull = elabElimTm params (lvl cxt_params) vDescSum

    let vElimTy = evalTy (env cxt) elimTyFull
    let vElimTm = evalTm (env cxt) elimTmFull

    let elimName = "elim" ++ x
    let cxt_final = define elimName vElimTm vElimTy cxt_with_constrs

    (uTm, uTy) <- infer cxt_final u

    let nfElimTy = quoteTy (lvl cxt_with_constrs) vElimTy
    let nfElimTm = quoteTm (lvl cxt_with_constrs) vElimTm

    let finalTm = Let x tyD term_D $
                  wrapLets $
                  Let elimName nfElimTy nfElimTm uTm
    pure (finalTm, uTy)

  RPair {} -> report cxt "Can't infer type for Pair"
  RU {} -> report cxt "Can't infer type for universe"
  RPi {} -> report cxt "Can't infer type for product type"
  RLam {} -> report cxt "Can't infer type for lambda expression."

-- printing
--------------------------------------------------------------------------------

fresh :: [Name] -> Name -> Name
fresh ns "_" = "_"
fresh ns x | elem x ns = go (1 :: Int) where
  go n | elem (x ++ show n) ns = go (n + 1)
       | otherwise             = x ++ show n  
fresh ns x = x

atomp = 3  :: Int -- U, var
appp  = 2  :: Int -- application
pip   = 1  :: Int -- pi
letp  = 0  :: Int -- let, lambda

par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

prettyTm :: Int -> [Name] -> Tm -> ShowS
prettyTm = goTm where
  goTm :: Int -> [Name] -> Tm -> ShowS
  goTm p ns = \case
    Var (Ix x) ->
      if x < 0 || x >= length ns then 
        (("Free" ++ show x) ++)
      else case ns !! x of
        "_"   -> ("@"++).(show x++)
        n     -> (n++)

    App t u -> par p appp $ goTm appp ns t . (' ':) . goTm atomp ns u

    Lam (fresh ns -> x) t -> par p letp $ ("λ "++) . (x++) . goLam (x:ns) t where
      goLam ns (Lam (fresh ns -> x) t) = (' ':) . (x++) . goLam (x:ns) t
      goLam ns t = (". "++) . goTm letp ns t

    Fst t -> par p appp $ ("fst "++) . goTm atomp ns t
    Snd t -> par p appp $ ("snd "++) . goTm atomp ns t

    Code i t -> ('[':).prettyTy letp ns t.(']':)

    Let (fresh ns -> x) a t u ->
      par p letp $ ("let "++) . (x++) . (" : "++) . prettyTy letp ns a
      . ("\n    = "++) . goTm letp ns t . ("\n;\n"++) . goTm letp (x:ns) u

    Pair t u -> par p appp $ ("⟨"++) . goTm letp ns t . (", "++) . goTm letp ns u . ("⟩"++)

    DPair _ t u -> par p appp $ ("⟨"++) . goTm letp ns t . (", "++) . goTm letp ns u . ("⟩"++)

    One -> ("*"++)

    ConLabel cName t ->
      let extractArgs One = []
          extractArgs (Pair a b) = a : extractArgs b
          extractArgs (DPair _ a b) = a : extractArgs b
          extractArgs _ = []
      in case t of
        In (DPair _ _ payload) ->
          let args = extractArgs payload
          in if null args 
             then (cName++)
             else par p appp $ (cName++) . foldr (\arg acc -> (' ':) . goTm atomp ns arg . acc) id args
        _ -> par p appp $ (cName++) . (' ':) . goTm atomp ns t

    In t -> par p appp $ ("in "++) . goTm atomp ns t

    SquareMap d f m -> par p appp $ ("map◻ "++) . prettyDesc atomp ns d . (' ':) . goTm atomp ns f . (' ':) . goTm atomp ns m

    ExtMap d f m -> par p appp $ ("map⟦⟧ "++) . prettyDesc atomp ns d . (' ':) . goTm atomp ns f . (' ':) . goTm atomp ns m

    Elim d c m n -> par p appp $ ("elim "++) . prettyDesc atomp ns d . (' ':) . goTm atomp ns c . (' ':) . goTm atomp ns m . (' ':) . goTm atomp ns n

    DReturn d -> par p appp $ ("return "++) . prettyDesc atomp ns d

    NilE -> ("nil"++)

    ConsE n t -> par p appp $ ("cons "++) . (n++) . (' ':) . goTm atomp ns t

    ZeroE -> ("0"++)

    SuccE t -> par p appp $ ("1 + "++) . goTm atomp ns t

    Switch t u -> par p appp $ ("switch "++) . goTm atomp ns t . (' ':) . goTm atomp ns u

prettyTy :: Int -> [Name] -> Ty -> ShowS
prettyTy = goTy where
  piBind ns x a = showParen True ((x++) . (" : "++) . goTy letp ns a)
  
  goTy :: Int -> [Name] -> Ty -> ShowS
  goTy p ns = \case    
    U Big -> ("Tp"++)
    U i -> par p appp $ ("U "++).(show i++)

    Pi "_" a b -> par p pip $ goTy appp ns a . (" → "++) . goTy pip ("_":ns) b

    Pi (fresh ns -> x) a b -> par p pip $ ("Π "++) . piBind ns x a . goPi (x:ns) b where
      goPi ns (Pi "_" a b) = (". "++) . goTy appp ns a . (" → "++) . goTy pip ("_":ns) b
      goPi ns (Pi x a b) = piBind ns x a . goPi (x:ns) b
      goPi ns b = (". "++) . goTy pip ns b

    Decode i t -> ('<':).prettyTm letp ns t.('>':)

    Unit -> ("1"++)

    Tensor a b -> par p appp $ goTy atomp ns a . (" × "++) . goTy atomp ns b

    Sigma "_" a b -> par p pip $ goTy appp ns a . (" × "++) . goTy pip ("_":ns) b

    Sigma (fresh ns -> x) a b -> par p pip $ ("Σ "++) . piBind ns x a . (". "++) . goTy pip (x:ns) b

    Ext d x -> par p appp $ ("⟦ "++) . prettyDesc letp ns d . (" ⟧ "++) . goTy atomp ns x

    Mu d -> par p appp $ ("μ "++) . prettyDesc atomp ns d

    Square d pr m -> par p appp $ ("◻ "++) . prettyDesc atomp ns d . (' ':) . goTy atomp ("_":ns) pr . (' ':) . prettyTm atomp ns m

    DLabel (Data n ts) _ -> 
      if null ts
      then (n++)
      else par p appp $ (n++) . foldr (\t acc -> (' ':) . prettyTm atomp ns t . acc) id ts

    EnumU -> ("EnumU "++)

    EnumT t -> par p appp $ ("Enum "++) . prettyTm atomp ns t

    SmallPiE t u -> par p appp $ ("π_E "++) . prettyTm atomp ns t . (' ':) . prettyTm atomp ns u

prettyDesc :: Int -> [Name] -> Desc -> ShowS
prettyDesc = goDesc where
  goDesc :: Int -> [Name] -> Desc -> ShowS
  goDesc p ns = \case
    DescUnit -> ("1"++)

    DescVar -> ("X"++)

    DescTensor d1 d2 -> par p appp $ goDesc atomp ns d1 . (" ⊗  "++) . goDesc atomp ns d2

    DescSum (fresh ns -> x) a d -> par p pip $ ("Σ "++) . showParen True ((x++) . (" : "++) . prettyTy letp ns a) . (". "++) . goDesc pip (x:ns) d

    DescProd (fresh ns -> x) a d -> par p pip $ ("Π "++) . showParen True ((x++) . (" : "++) . prettyTy letp ns a) . (". "++) . goDesc pip (x:ns) d

    DescCall (Data n _) t -> par p appp $ (n++) . (' ':) . prettyTm atomp ns t

-- parsing
--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Raw -> Parser Raw
withPos p = RSrcPos <$> getSourcePos <*> p

lexeme   = L.lexeme ws
symbol s = lexeme (C.string s)
char c   = lexeme (C.char c)
parens p = char '(' *> p <* char ')'
pArrow   = symbol "→" <|> symbol "->"
decimal  = lexeme L.decimal

keyword :: String -> Bool
keyword x = x `elem` ["let", "λ", "U", "Tp", "data", "where", "fst", "snd"]

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pAtom :: Parser Raw
pAtom =
      withPos (
            (RVar <$> pIdent)
        <|> (RU . Sz <$> (pKeyword "U" *> decimal))
        <|> (RU Big <$ pKeyword "Tp")
        <|> (ROne <$ symbol "*")
        <|> (RFst <$> (pKeyword "fst" *> pAtom))
        <|> (RSnd <$> (pKeyword "snd" *> pAtom))
        <|> try (do
              symbol "⟨" <|> symbol "<"
              t <- pRaw
              symbol ","
              u <- pRaw
              symbol "⟩" <|> symbol ">"
              pure (RPair t u))
      )
  <|> parens pRaw

pTele :: Parser [(Name, Raw)]
pTele = concat <$> many (parens ((\xs a -> map (\x -> (x, a)) xs) <$> some pBinder <*> (symbol ":" *> pRaw)))

pData :: Parser Raw
pData = do
  pKeyword "data"
  x <- pBinder
  params <- pTele
  symbol ":"
  ty <- pRaw
  pKeyword "where"
  char '{'
  constrs <- sepEndBy1 ((,) <$> pBinder <*> (symbol ":" *> pRaw)) (char ';')
  char '}'
  char ';'
  u <- pRaw
  pure $ RData x params ty (NE.fromList constrs) u

pBinder = pIdent <|> symbol "_"

pSpine  = foldl1 RApp <$> some pAtom

pLam = do
  char 'λ' <|> char '\\'
  xs <- some pBinder
  char '.'
  t <- pRaw
  pure (foldr RLam t xs)

pPi = do
  dom <- some (parens ((,) <$> some pBinder <*> (char ':' *> pRaw)))
  pArrow
  cod <- pRaw
  pure $ foldr (\(xs, a) t -> foldr (\x -> RPi x a) t xs) cod dom

funOrSpine = do
  sp <- pSpine
  res <- optional (symbol "@" *> decimal)
  let sp' = case res of
              Just i -> RAt sp (Sz i)
              Nothing -> sp
  optional pArrow >>= \case
    Nothing -> pure sp'
    Just _  -> RPi "_" sp' <$> pRaw

pLet = do
  pKeyword "let"
  x <- pBinder
  symbol ":"
  a <- pRaw
  symbol "="
  t <- pRaw
  char ';'
  u <- pRaw
  pure $ RLet x a t u

pRaw = withPos (pLam <|> pLet <|> pData <|> try pPi <|> funOrSpine)
pSrc = ws *> pRaw <* eof

parseString :: String -> IO Raw
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitSuccess
    Right t ->
      pure t

parseStdin :: IO (Raw, String)
parseStdin = do
  file <- getContents
  tm   <- parseString file
  pure (tm, file)

-- main
--------------------------------------------------------------------------------

displayError :: String -> (String, SourcePos) -> IO ()
displayError file (msg, SourcePos path (unPos -> linum) (unPos -> colnum)) = do
  let lnum = show linum
      lpad = map (const ' ') lnum
  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg

helpMsg :: String
helpMsg = unlines [
  "usage: elabzoo-univ-lifts <mode> <filepath>",
  "modes:",
  "  nf <file>      : read & elaborate expression from file, print its normal form and type",
  "  elab <file>    : read & elaborate expression from file, print output",
  "  type <file>    : read & elaborate expression from file, print its type",
  "",
  "example:",
  "  runhaskell Datatypes.hs nf test/ex1.txt"
  ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> putStrLn helpMsg
    
    [mode, filepath] | mode `elem` ["nf", "elab", "type"] -> do
      src <- readFile filepath
      
      case parse pSrc filepath src of
        Left e -> putStrLn $ errorBundlePretty e
        Right tm -> do
          
          let cxt = emptyCxt (initialPos filepath)
          case infer cxt tm of
            Left err -> displayError src err
            Right (t, a) -> case mode of
              "nf" -> do
                putStrLn $ showTm0 $ nf [] t
                putStrLn "  :"
                putStrLn $ showTy0 $ quoteTy 0 a
              "elab" -> putStrLn $ showTm0 $ t
              "type" -> putStrLn $ showTy0 $ quoteTy 0 a
              _      -> pure ()
              
    _ -> putStrLn helpMsg