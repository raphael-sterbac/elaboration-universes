
module Main where

import Prelude hiding (lookup)
import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Void
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import System.Environment ()
import System.Exit
import Text.Megaparsec
import Text.Printf

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

-- import Debug.Trace

-- examples
--------------------------------------------------------------------------------

ex0 = main' "nf" $ unlines [

  "data Bool : U 0 where {",
  "  true : Bool ;",
  "  false : Bool",
  "} ;",

  "data List (A : U 0) : U 0 where {",
  "  nil : List A ;",
  "  cons : A -> List A -> List A",
  "} ;",

  "let f : U 1 -> U 1 = \\A. A;",
  "let g : U 0 -> U 2 = f;",
  "let f : (A : U 0) -> A -> A = \\A x. x;",

  "let IdTy1    : U 2 = ((A : U 1) -> A -> A);",
  "let ConstTy0 : U 1 = ((A B : U 0) -> A -> B -> A);",
  "let id1 : IdTy1 = \\A x. x;",
  "let const0 : ConstTy0 = \\A B x y. x;",
  "let foo : ConstTy0 = id1 ConstTy0 const0;",

  "let Nat  : U 1 = ((N : U 0) -> ( N -> N) -> N -> N) ;",
  "let zero : Nat = λ N s z. z;",
  "let one  : Nat = λ N s z. s z;",
  "let five : Nat = \\N s z. s (s (s (s (s z)))) ;",
  "let add  : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z) ;",
  "let mul  : Nat -> Nat -> Nat = \\a b N s z. a N (b N s) z ;",
  "let ten      : Nat = add five five ;",
  "let hundred  : Nat = mul ten ten ;",

  "let Eq1 : (A : U 1) → A → A → U 1",
  "    = λ A x y. ((P : A → U 0) → (P x) → (P y) );",

  "let refl1 : (A : U 1)(x : A) → Eq1 A x x",
  "  = λ A x P px. px;",

  "let p1 : Eq1 Nat ten ten = refl1 Nat ten;",
  "id1 Nat hundred"

  ]


-- syntax
--------------------------------------------------------------------------------

-- | De Bruijn index.
newtype Ix  = Ix  Int deriving (Eq, Show, Num) via Int

-- | De Bruijn level.
newtype Lvl = Lvl Int deriving (Eq, Show, Num) via Int


type Name = String

data Raw
  = RVar Name              -- x
  | RLam Name Raw          -- \x. t
  | RApp Raw Raw           -- t u
  | RU Int                 -- U i
  | RPi Name Raw Raw       -- (x : A) -> B
  | RLet Name Raw Raw Raw  -- let x : A = t in u
  | RSrcPos SourcePos Raw  -- source position for error reporting
  | RData Name [(Name, Raw)] Raw (NonEmpty (Name, Raw)) Raw -- Datatype definition
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
    | U Int 
    | Decode Int Tm
    | Unit
    | Sigma Name ~Ty Ty
    | Tensor Ty Ty
    -- Descriptions
    | Ext Desc Ty
    | Mu Desc
    | Square Desc ~Ty Tm
    | DLabel Label
    -- Enumerations
    | EnumU
    | EnumT Tm
    | SmallPiE Tm Tm

data Tm
  = Var Ix
  | App Tm ~Tm
  | Code Int Ty
  | Lam Name Tm
  | Let Name Ty Tm Tm
  | Pair Tm Tm
  | DPair Name Tm Tm
  | One
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

data VTy
  = VPi Name ~VTy (VTm -> VTy)
    | VU Int 
    | VDecode Int VTm
    | VSigma Name VTy (VTm -> VTy)
    | VUnit
    -- Descriptions
    | VTensor VTy VTy
    | VSquare VDesc (VTm -> VTy) VTm
    | VMu Env VDesc
    | VDLabel Label
    -- Enumerations
    | VEnumU
    | VEnumT VTm
    | VSmallPiE VTm VTm
    

data VTm
  = VVar Lvl
  | VApp VTm ~VTm
  | VCode Int VTy
  | VLam Name (VTm -> VTm)
  | VPair VTm VTm
  | VDPair Name VTm VTm
  | VOne
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
  | VDescCall Label VTm

--------------------------------------------------------------------------------

vApp :: VTm -> VTm -> VTm
vApp (VLam _ f) v = f v
vApp f          v = VApp f v

-- External functions for descriptions
applyExtMap :: VDesc -> VTm -> VTm -> VTm
applyExtMap d vf vm = case d of
  VDescUnit -> VOne
  
  VDescVar -> vApp vf vm
  
  VDescTensor e1 e2 -> case vm of
    VPair va vb -> VPair (applyExtMap e1 vf va) (applyExtMap e2 vf vb)
    k     -> VExtMap d vf k
    
  VDescSum n a d1 -> case vm of
    VDPair n' p1 p2 -> VDPair n' p1 (applyExtMap (d1 p1) vf p2)
    k         -> VExtMap d vf k
    
  VDescProd n a d -> VLam n \v -> applyExtMap (d v) vf (vApp vm v)

applySquareMap :: VDesc -> VTm -> VTm -> VTm
applySquareMap d vf vm = case d of
  VDescUnit -> VOne
  
  VDescVar -> vApp vf vm
  
  VDescTensor d1 d2 -> case vm of
    VPair v1 v2 -> VPair (applySquareMap d1 vf v1) (applySquareMap d2 vf v2)
    k     -> VSquareMap d vf k
    
  VDescSum n a d1 -> case vm of
    VDPair _ p1 p2 -> applySquareMap (d1 p1) vf p2
    k        -> VSquareMap d vf k
    
  VDescProd n a d1 -> case vm of
    VLam n' f -> VLam n' \v -> applySquareMap (d1 v) vf (f v)
    k   -> VSquareMap d vf k

applyElim :: VDesc -> VTm -> VTm -> VTm -> VTm
applyElim d vc vm vn = case vn of
  VIn x -> 
    let recElim = VLam "_" \v -> applyElim d vc vm v
        ihs = applySquareMap d recElim x
    in vApp (vApp vm x) ihs
    
  k -> VElim d vc vm k

applySwitch :: VTm -> VTm -> VTm
applySwitch vt vu = case vu of
  VZeroE -> case vt of
    VPair v1 _    -> v1
    VDPair _ v1 _ -> v1
    k       -> VSwitch k VZeroE
    
  VSuccE x -> case vt of
    VPair _ v2    -> applySwitch v2 x
    VDPair _ _ v2 -> applySwitch v2 x
    k       -> VSwitch k (VSuccE x)
    
  k -> VSwitch vt k

evalTm :: Env -> Tm -> VTm
evalTm env = \case
  Var (Ix x)    -> env !! x
  App t u       -> vApp (evalTm env t) (evalTm env u)
  Lam x t       -> VLam x \v -> evalTm (v:env) t
  Let x _ t u -> evalTm (evalTm env t : env) u
  Pair t u      -> VPair (evalTm env t) (evalTm env u)
  DPair x t u   -> VDPair x (evalTm env t) (evalTm env u)
  One           -> VOne
  In t          -> VIn (evalTm env t)

  -- Case of a Coding
  Code i a      -> VCode i (evalTy env a)
  
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

applySquare :: Env -> Desc -> (VTm -> VTy) -> VTm -> VTy
applySquare env d p vm = case d of
  DescUnit -> VUnit 

  DescVar -> p vm

  DescTensor d e -> case vm of
    VPair a b -> VTensor (applySquare env d p a) (applySquare env e p b)
    k     -> VSquare (VDescTensor (evalDesc env d) (evalDesc env e)) p k

  DescSum n a d1 -> case vm of
    VDPair _ p1 p2 -> applySquare env d1 p p2
    k        -> VSquare (evalDesc env d) p k
    
  DescProd n a d1 ->  VPi n (evalTy env a) \v -> applySquare env d1 p (vApp vm v)


evalTy :: Env -> Ty -> VTy
evalTy env = \case
  Pi x a b      -> VPi x (evalTy env a) \v -> evalTy (v:env) b
  U i           -> VU i
  Sigma x a b   -> VSigma x (evalTy env a) \v -> evalTy (v:env) b
  Tensor a b    -> VTensor (evalTy env a) (evalTy env b)
  Unit          -> VUnit

  -- Case of a Decoding
  Decode i t    -> case evalTm env t of
    VCode j a | i == j  -> a             -- Beta Rule for the Universe
    v                   -> VDecode i v

  -- Descriptions
  Ext d x -> case d of
    DescUnit -> VUnit 
    DescVar -> evalTy env x
    DescTensor d e -> VTensor (evalTy env (Ext d x)) (evalTy env (Ext e x))
    DescSum n a d -> VSigma n (evalTy env a) \v -> evalTy (v:env) (Ext d x)
    DescProd n a d -> VPi n (evalTy env a) \v -> evalTy (v:env) (Ext d x) 

  Square d p m ->
    let vp = \v -> evalTy (v:env) p
        vm = evalTm env m
    in applySquare env d vp vm

  Mu d -> VMu env (evalDesc env d)

  DLabel l -> VDLabel l
  
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

  DescCall l t -> case (evalTm env t) of
    VDReturn d -> d
    k -> VDescCall l k


lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quoteTm :: Lvl -> VTm -> Tm
quoteTm l = \case
  VVar x      -> Var (lvl2Ix l x)
  VApp t u    -> App (quoteTm l t) (quoteTm l u)
  VLam x t    -> Lam x (quoteTm (l + 1) (t (VVar l)))
  VPair t u -> Pair (quoteTm l t) (quoteTm l u)
  VDPair x t u -> DPair x (quoteTm l t) (quoteTm l u)
  VOne -> One

  -- Case of a Coding
  VCode i a   -> Code i (quoteTy l a)

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
  VU i        -> U i
  VSigma x a b -> Sigma x (quoteTy l a) (quoteTy (l + 1) (b (VVar l)))
  VUnit -> Unit
  VTensor a b -> Tensor (quoteTy l a) (quoteTy l b)

  -- Case of a Decoding
  VDecode i t -> Decode i (quoteTm l t)

  -- Descriptions
  VSquare d p m -> Square (quoteDesc l d) (quoteTy (l + 1) (p (VVar l))) (quoteTm l m)
  VMu _ d -> Mu (quoteDesc l d)
  VDLabel l -> DLabel l

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
  VDescCall lbl t -> DescCall lbl (quoteTm l t)

nf :: Env -> Tm -> Tm
nf env t = quoteTm (Lvl (length env)) (evalTm env t)

convTm :: Lvl -> VTm -> VTm -> Bool
convTm l t u = case (t, u) of
  (VLam _ t, VLam _ t') -> convTm (l + 1) (t (VVar l)) (t' (VVar l))

  (VLam _ t, u) -> convTm (l + 1) (t (VVar l)) (VApp u (VVar l))
  (u, VLam _ t) -> convTm (l + 1) (VApp u (VVar l)) (t (VVar l))

  (VVar x  , VVar x'   ) -> x == x'
  (VApp t u, VApp t' u') -> convTm l t t' && convTm l u u'

  (VPair t1 u1, VPair t2 u2) -> convTm l t1 t2 && convTm l u1 u2
  (VDPair _ t1 u1, VDPair _ t2 u2) -> convTm l t1 t2 && convTm l u1 u2
  (VOne, VOne) -> True

  (VCode i a, VCode j b) | i == j -> convTy l a b

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
convTy l t u = case (t, u) of
  (VU i, VU i') -> i == i'
  (VUnit, VUnit) -> True
  (VTensor a b, VTensor a' b') -> convTy l a a' && convTy l b b'


  (VPi _ a b, VPi _ a' b') -> convTy l a a' && convTy (l + 1) (b (VVar l)) (b' (VVar l))
  (VSigma _ a b, VSigma _ a' b') -> convTy l a a' && convTy (l + 1) (b (VVar l)) (b' (VVar l))
  (VDecode i a, VDecode j b) | i == j -> convTm l a b

  -- Descriptions
  (VSquare d p m, VSquare d' p' m') -> convDesc l d d'  && convTy (l + 1) (p (VVar l)) (p' (VVar l))  && convTm l m m'
  (VMu _ d, VMu _ d') -> convDesc l d d'
  (VDLabel (Data n _), VDLabel (Data n' _)) -> n == n' -- TODO : Maybe I should also try to equate the parameters here, not sure

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
  (VDescCall (Data n _) t, VDescCall (Data n' _) t') -> n == n' && convTm l t t' -- TODO : Maybe I should also try to equate the parameters here, not sure
  _ -> False


-- Elaboration
--------------------------------------------------------------------------------

-- type of every variable in scope
type Types = [(Name, VTy)]

-- | Elaboration context.
data Cxt = Cxt {env :: Env, types :: Types, lvl :: Lvl, pos :: SourcePos}

emptyCxt :: SourcePos -> Cxt
emptyCxt = Cxt [] [] 0

-- | Extend Cxt with a bound variable.
bind :: Name -> VTy -> Cxt -> Cxt
bind x ~a (Cxt env types l pos) =
  Cxt (VVar l:env) ((x, a):types) (l + 1) pos

-- | Extend Cxt with a definition.
define :: Name -> VTm -> VTy -> Cxt -> Cxt
define x ~t ~a (Cxt env types l pos) =
  Cxt (t:env) ((x, a):types) (l + 1) pos

-- | Typechecking monad. We annotate the error with the current source position.
type M = Either (String, SourcePos)


-- Printing and error reporting

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

-- showTm cxt t = show t

showTm0 :: Tm -> String
showTm0 t = prettyTm 0 [] t []

showTy0 :: Ty -> String
showTy0 a = prettyTy 0 [] a []

showVal :: Cxt -> VTm -> String
showVal cxt v = showTm cxt $ quoteTm (lvl cxt) v


showVTy :: Cxt -> VTy -> String
showVTy cxt v = showTy cxt $ quoteTy (lvl cxt) v

--------------------------------------------------------------------------------

inferU :: Cxt -> Raw -> M (Tm, Int)
inferU cxt t = do
  (t, a) <- infer cxt t
  case a of
    VU i -> pure (t, i)
    _    -> report cxt "expected a type"


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
    let vApp = case vm of
                VLam _ f -> f vu_x
                _        -> VApp vm vu_x
    let m_u_x = quoteTm l' vApp
    
    n_x <- coe cxt' l' (b1 vu_x) (b2 (VVar l)) m_u_x
    
    pure $ Lam n2 n_x

  _ -> 
    if convTy l sourceTy targetTy then
      pure m 
    else report cxt "Error: Invalid coercion"

checkTy :: Cxt -> Raw -> Maybe Int -> M Ty
checkTy cxt t size = case t of

  RSrcPos pos t -> checkTy (cxt {pos = pos}) t size

  RU i -> case size of 
    Nothing -> pure $ U i
    Just j | i < j -> pure $ U i
    Just k -> report cxt ("Size issue: U " ++ show i ++ ", but expected a universe in U " ++ show k)

  RPi x a b -> do
    a' <- checkTy cxt a size
    let cxt' = bind x (evalTy (env cxt) a') cxt
    b' <- checkTy cxt' b size
    pure $ Pi x a' b'

  -- mode switch
  _ -> do 
    (t, a) <- infer cxt t
    case a of
      VU i -> case size of 
        Nothing -> pure (Decode i t)
        Just j | i <= j -> pure (Decode i t)
        Just k -> report cxt ("Size issue: got a code at level " ++ show i ++ ", but expected  " ++ show k)
      _    -> report cxt "Elaboration error: Expected a code"
    


check :: Cxt -> Raw -> VTy -> M Tm
check cxt t a = case (t, a) of
  (RSrcPos pos t, a) -> check (cxt {pos = pos}) t a

  (RLam x t, VPi x' a b) ->
    Lam x <$> check (bind x a cxt) t (b (VVar (lvl cxt)))

  (_, VU i) -> do
    u <- checkTy cxt t (Just i)
    pure $ Code i u

  (RLet x a t u, a') -> do
    a <- checkTy cxt a Nothing
    let ~va = evalTy (env cxt) a
    t <- check cxt t va
    let ~vt = evalTm (env cxt) t
    u <- check (define x vt va cxt) u a' 
    pure (Let x a t u)

  -- mode switch
  _ -> do
    (m, bTy) <- infer cxt t
    coe cxt (lvl cxt) bTy a m
    
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
    (t, tty) <- infer cxt t
    case tty of
      VPi _ a b -> do
        u <- check cxt u a
        pure (App t u, b (evalTm (env cxt) u))
      tty ->
        report cxt $ "Expected a function type, instead inferred:\n\n  " ++ showVTy cxt tty

  RLet x a t u -> do
    a <- checkTy cxt a Nothing
    let ~va = evalTy (env cxt) a
    t <- check cxt t va
    let ~vt = evalTm (env cxt) t
    (u, uty) <- infer (define x vt va cxt) u  
    pure (Let x a t u, uty)

  RData x params ty constrs u ->
    report cxt "TODO."


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
      case ns !! x of
        "_"   -> ("@"++).(show x++)
        n     -> (n++)

    App t u -> par p appp $ goTm appp ns t . (' ':) . goTm atomp ns u

    Lam (fresh ns -> x) t -> par p letp $ ("λ "++) . (x++) . goLam (x:ns) t where
      goLam ns (Lam (fresh ns -> x) t) = (' ':) . (x++) . goLam (x:ns) t
      goLam ns t = (". "++) . goTm letp ns t

    Code i t -> ('[':).prettyTy letp ns t.(']':)

    Let (fresh ns -> x) a t u ->
      par p letp $ ("let "++) . (x++) . (" : "++) . prettyTy letp ns a
      . ("\n    = "++) . goTm letp ns t . ("\n;\n"++) . goTm letp (x:ns) u

    Pair t u -> par p appp $ ("⟨"++) . goTm letp ns t . (", "++) . goTm letp ns u . ("⟩"++)

    DPair _ t u -> par p appp $ ("⟨"++) . goTm letp ns t . (", "++) . goTm letp ns u . ("⟩"++)

    One -> ("*"++)

    In t -> par p appp $ ("in "++) . goTm atomp ns t

    SquareMap d f m -> par p appp $ ("map◻ "++) . prettyDesc atomp ns d . (' ':) . goTm atomp ns f . (' ':) . goTm atomp ns m

    ExtMap d f m -> par p appp $ ("map⟦⟧ "++) . prettyDesc atomp ns d . (' ':) . goTm atomp ns f . (' ':) . goTm atomp ns m

    Elim d c m n -> par p appp $ ("elim "++) . prettyDesc atomp ns d . (' ':) . goTm atomp ns c . (' ':) . goTm atomp ns m . (' ':) . goTm atomp ns n

    NilE -> ("nil"++)

    ConsE n t -> par p appp $ ("cons "++) . (n++) . (' ':) . goTm atomp ns t

    ZeroE -> ("0"++)

    SuccE t -> par p appp $ ("1+ "++) . goTm atomp ns t

    Switch t u -> par p appp $ ("switch "++) . goTm atomp ns t . (' ':) . goTm atomp ns u


prettyTy :: Int -> [Name] -> Ty -> ShowS
prettyTy = goTy where
  piBind ns x a = showParen True ((x++) . (" : "++) . goTy letp ns a)
  
  goTy :: Int -> [Name] -> Ty -> ShowS
  goTy p ns = \case    
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

    DLabel (Data n _) -> (n++)

    EnumU -> ("EnumU "++)

    EnumT t -> par p appp $ ("Enum "++) . prettyTm atomp ns t

    SmallPiE t u -> par p appp $ ("π_E "++) . prettyTm atomp ns t . (' ':) . prettyTm atomp ns u

prettyDesc :: Int -> [Name] -> Desc -> ShowS
prettyDesc = goDesc where
  goDesc :: Int -> [Name] -> Desc -> ShowS
  goDesc p ns = \case
    DescUnit -> ("1"++)

    DescVar -> ("X"++)

    DescTensor d1 d2 -> par p appp $ goDesc atomp ns d1 . (" ⊗ "++) . goDesc atomp ns d2

    DescSum (fresh ns -> x) a d -> par p pip $ ("Σ "++) . showParen True ((x++) . (" : "++) . prettyTy letp ns a) . (". "++) . goDesc pip (x:ns) d

    DescProd (fresh ns -> x) a d -> par p pip $ ("Π "++) . showParen True ((x++) . (" : "++) . prettyTy letp ns a) . (". "++) . goDesc pip (x:ns) d

    DescCall (Data n _) t -> par p appp $ (n++) . (' ':) . prettyTm atomp ns t

-- instance Show Tm where showsPrec p = prettyTm p []


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
keyword x = x == "let" || x == "λ" || x == "U" || x == "data" || x == "where"

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
        <|> (RU <$> (pKeyword "U" *> decimal))
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
  optional pArrow >>= \case
    Nothing -> pure sp
    Just _  -> RPi "_" sp <$> pRaw

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

helpMsg = unlines [
  "usage: elabzoo-univ-lifts [--help|nf|type]",
  "  --help         : display this message",
  "  nf             : read & elaborate expression from stdin, print its normal form and type",
  "  elab           : read & elaborate expression from stdin, print output",
  "  elab-no-delift : read & elaborate expression from stdin, print output",
  "                   without removing intermediate lifts and explicit weakenings",
  "  type           : read & elaborate expression from stdin, print its type"]

mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getRaw = do
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"]   -> do
      (t, file) <- getRaw
      case infer (emptyCxt (initialPos file)) t of
        Left err -> displayError file err
        Right (t, a) -> do
          putStrLn $ showTm0 $ nf [] t
          putStrLn "  :"
          putStrLn $ showTy0 $ quoteTy 0 a
    ["elab"] -> do
      (t, file) <- getRaw
      case infer (emptyCxt (initialPos file)) t of
        Left err     -> displayError file err
        Right (t, a) -> putStrLn $ showTm0 $ t
    ["type"] -> do
      (t, file) <- getRaw
      case infer (emptyCxt (initialPos file)) t of
        Left err     -> displayError file err
        Right (t, a) -> putStrLn $ showTy0 $ quoteTy 0 a
    _ -> putStrLn helpMsg

main :: IO ()
main = ex0

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)