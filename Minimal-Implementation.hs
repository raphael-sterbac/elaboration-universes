{-# LANGUAGE LambdaCase, BlockArguments, ViewPatterns, TupleSections, StandaloneDeriving, DerivingVia, StrictData #-}
module Main where

import Prelude hiding (lookup)
import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Void
import System.Environment ()
import System.Exit
import Text.Megaparsec
import Text.Printf

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L



ex0 = main' "nf" $ unlines [

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

-- De Bruijn index.
newtype Ix  = Ix  Int deriving (Eq, Show, Num) via Int

-- De Bruijn level.
newtype Lvl = Lvl Int deriving (Eq, Show, Num) via Int

type Name = String

data RawSize = RSzVar Name | RSz Int | RSucc RawSize | RBig | ROmega deriving Show
data Size = LVar Ix | Sz Int | Succ Size | Big | Omega 

data SizeFlattened = FZero Int | FVar Ix Int | FBig | FOmega deriving (Eq)

flattenSize :: Size -> SizeFlattened
flattenSize (Sz i) = FZero i
flattenSize (LVar x) = FVar x 0
flattenSize Big = FBig
flattenSize Omega = FOmega
flattenSize (Succ s) = case flattenSize s of
  FZero n -> FZero (n + 1)
  FVar x n -> FVar x (n + 1)
  FBig -> FBig     
  FOmega -> FOmega  

instance Eq Size where
  (==) :: Size -> Size -> Bool
  s1 == s2 = flattenSize s1 == flattenSize s2

instance Ord Size where
  s1 <= s2 = case (flattenSize s1, flattenSize s2) of
    (_, FOmega) -> True
    (FOmega, _) -> False
    (_, FBig) -> True
    (FBig, _) -> False
    (FZero n, FZero m) -> n <= m
    (FZero n, FVar _ m) -> n <= m
    (FVar _ _, FZero _) -> False
    (FVar x n, FVar y m) -> x == y && n <= m
    
  s1 < s2 = s1 <= s2 && not (s2 <= s1)

instance Show Size where
  show (LVar i) = show i
  show (Sz i) = show i
  show (Succ s) = show s ++ " + 1"
  show Big    = "Tp"
  show Omega  = "Omega"

data Raw
  = RVar Name              -- x
  | RLam Name Raw          -- \x. t
  | RApp Raw Raw           -- t u
  | RU RawSize             -- U i
  | RPi Name Raw Raw       -- (x : A) -> B
  | RLPi Name Raw          -- ∀ l. A
  | RLAbs Name Raw         -- Λ l. t
  | RLApp Raw RawSize      -- t {s}
  | RLet Name Raw Raw Raw  -- let x : A = t in u
  | RSrcPos SourcePos Raw  -- source position for error reporting
  deriving Show

-- core syntax
------------------------------------------------------------

data Ty
  = Pi Name ~Ty Ty
    | U Size 
    | Decode Size Tm
    | LPi Name Ty

data Tm
  = Var Ix
  | App Tm ~Tm
  | Code Size Ty
  | Lam Name Tm
  | Let Name Ty Tm Tm
  | LAbs Name Tm
  | LApp Tm Size

-- values
------------------------------------------------------------

data VSize = VLVar Lvl | VSz Int | VSucc VSize | VBig | VOmega 

data VSizeFlattened = FVZero Int | FVVar Lvl Int | FVBig | FVOmega deriving (Eq)

flattenVSize :: VSize -> VSizeFlattened
flattenVSize (VSz i) = FVZero i
flattenVSize (VLVar x) = FVVar x 0
flattenVSize VBig = FVBig
flattenVSize VOmega = FVOmega
flattenVSize (VSucc s) = case flattenVSize s of
  FVZero n -> FVZero (n + 1)
  FVVar x n -> FVVar x (n + 1)
  FVBig -> FVBig
  FVOmega -> FVOmega

instance Eq VSize where
  s1 == s2 = flattenVSize s1 == flattenVSize s2

instance Ord VSize where
  s1 <= s2 = case (flattenVSize s1, flattenVSize s2) of
    (_, FVOmega) -> True
    (FVOmega, _) -> False
    (_, FVBig) -> True
    (FVBig, _) -> False
    (FVZero n, FVZero m) -> n <= m
    (FVZero n, FVVar _ m) -> n <= m
    (FVVar _ _, FVZero _) -> False
    (FVVar x n, FVVar y m) -> x == y && n <= m
    
  s1 < s2 = s1 <= s2 && not (s2 <= s1)

instance Show VSize where
  show (VLVar i) = show i
  show (VSz i) = show i
  show (VSucc s) = show s ++ " + 1"
  show VBig    = "Tp"
  show VOmega  = "Omega"

data VEnvVal = VETm VTm | VESize VSize
type Env = [VEnvVal]

data VTy
  = VPi Name ~VTy (VTm -> VTy)
    | VU VSize 
    | VDecode VSize VTm
    | VLPi Name (VSize -> VTy)

data VTm
  = VVar Lvl
  | VApp VTm ~VTm
  | VCode VSize VTy
  | VLam Name (VTm -> VTm)
  | VLAbs Name (VSize -> VTm)
  | VLApp VTm VSize

--------------------------------------------------------------------------------

evalSize :: Env -> Size -> VSize
evalSize env = \case
  LVar (Ix x) -> case env !! x of
    VESize s -> s
    _ -> error "Evaluation error: Expected a level variable in environment"
  Sz i -> VSz i 
  Succ s -> VSucc (evalSize env s)
  Big -> VBig
  Omega -> VOmega

evalTm :: Env -> Tm -> VTm
evalTm env = \case
  Var (Ix x) -> case env !! x of
                     VETm t -> t
                     _ -> error "Evaluation error: Expected a term variable in environment"
  App t u -> case (evalTm env t, evalTm env u) of
                     (VLam _ t, u) -> t u
                     (t       , u) -> VApp t u
  Lam x t -> VLam x \v -> evalTm (VETm v:env) t
  Let x _ t u -> evalTm (VETm (evalTm env t) : env) u
  LAbs x t -> VLAbs x \i -> evalTm (VESize i : env) t
  LApp t s -> case evalTm env t of
                     VLAbs _ f -> f (evalSize env s)
                     f -> VLApp f (evalSize env s)

  -- Case of a Coding
  Code i a -> VCode (evalSize env i) (evalTy env a)

evalTy :: Env -> Ty -> VTy
evalTy env = \case
  Pi x a b -> VPi x (evalTy env a) \v -> evalTy (VETm v:env) b
  U i -> VU (evalSize env i)
  LPi x t -> VLPi x \i -> evalTy (VESize i : env) t

  -- Case of a Decoding
  Decode i t -> case evalTm env t of
    VCode j a | evalSize env i == j -> a  -- Beta Rule for the Universe
    v -> VDecode (evalSize env i) v


lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quoteSize :: Lvl -> VSize -> Size
quoteSize l = \case
  VLVar x -> LVar (lvl2Ix l x)
  VSz i -> Sz i
  VSucc s -> Succ (quoteSize l s)
  VBig -> Big
  VOmega -> Omega

quoteTm :: Lvl -> VTm -> Tm
quoteTm l = \case
  VVar x -> Var (lvl2Ix l x)
  VApp t u -> App (quoteTm l t) (quoteTm l u)
  VLam x t -> Lam x (quoteTm (l + 1) (t (VVar l)))
  VLAbs x t -> LAbs x (quoteTm (l + 1) (t (VLVar l)))
  VLApp t s -> LApp (quoteTm l t) (quoteSize l s)

  -- Case of a Coding
  VCode i a -> Code (quoteSize l i) (quoteTy l a)

quoteTy :: Lvl -> VTy -> Ty
quoteTy l = \case
  VPi  x a b -> Pi x (quoteTy l a) (quoteTy (l + 1) (b (VVar l)))
  VU i -> U (quoteSize l i)
  VLPi x t -> LPi x (quoteTy (l + 1) (t (VLVar l)))

  -- Case of a Decoding
  VDecode i t -> Decode (quoteSize l i) (quoteTm l t)

nf :: Env -> Tm -> Tm
nf env t = quoteTm (Lvl (length env)) (evalTm env t)

convTm :: Lvl -> VTm -> VTm -> Bool
convTm l t u = case (t, u) of
  (VLam _ t, VLam _ t') ->
    convTm (l + 1) (t (VVar l)) (t' (VVar l))

  (VLam _ t, u) ->
    convTm (l + 1) (t (VVar l)) (VApp u (VVar l))
  (u, VLam _ t) ->
    convTm (l + 1) (VApp u (VVar l)) (t (VVar l))

  (VVar x  , VVar x'   ) -> x == x'
  (VApp t u, VApp t' u') -> convTm l t t' && convTm l u u'
  
  (VLAbs _ t, VLAbs _ t') -> convTm (l + 1) (t (VLVar l)) (t' (VLVar l))
  (VLApp t s, VLApp t' s') -> convTm l t t' && s == s'

  (VCode i a, VCode j b) | i == j -> convTy l a b

  _ -> False

convTy :: Lvl -> VTy -> VTy -> Bool
convTy l t u = case (t, u) of
  (VU i, VU i') -> i == i'

  (VPi _ a b, VPi _ a' b') ->
       convTy l a a'
    && convTy (l + 1) (b (VVar l)) (b' (VVar l))
    
  (VLPi _ a, VLPi _ a') -> convTy (l + 1) (a (VLVar l)) (a' (VLVar l))

  (VDecode i a, VDecode j b) | i == j -> convTm l a b

  _ -> False


-- Elaboration
--------------------------------------------------------------------------------

-- type of every variable in scope
type Types = [(Name, VTy)]

-- Elaboration context
data Cxt = Cxt {env :: Env, types :: Types, lvl :: Lvl, pos :: SourcePos}

emptyCxt :: SourcePos -> Cxt
emptyCxt = Cxt [] [] 0

-- Extend Cxt with a bound variable
bind :: Name -> VTy -> Cxt -> Cxt
bind x ~a (Cxt env types l pos) =
  Cxt (VETm (VVar l):env) ((x, a):types) (l + 1) pos

bindLevel :: Name -> Cxt -> Cxt
bindLevel x (Cxt env types l pos) =
  Cxt (VESize (VLVar l):env) ((x, VU (VSz 0)):types) (l + 1) pos
  
-- Extend Cxt with a definition
define :: Name -> VTm -> VTy -> Cxt -> Cxt
define x ~t ~a (Cxt env types l pos) =
  Cxt (VETm t:env) ((x, a):types) (l + 1) pos

-- Typechecking monad, We annotate the error with the current source position
type M = Either (String, SourcePos)


-- Printing and error reporting
report :: Cxt -> String -> M a
report cxt msg = Left (msg, pos cxt)

deriving instance Show Tm
deriving instance Show Ty

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

showSize :: Cxt -> VSize -> String
showSize cxt s = prettySize (map fst (types cxt)) (quoteSize (lvl cxt) s) ""

--------------------------------------------------------------------------------

vApp :: VTm -> VTm -> VTm
vApp (VLam _ f) v = f v
vApp f          v = VApp f v

inferU :: Cxt -> Raw -> M (Tm, Size)
inferU cxt t = do
  (t, a) <- infer cxt t
  case a of
    VU i -> pure (t, quoteSize (lvl cxt) i)
    _    -> report cxt "expected a type"


coe :: Cxt -> Lvl -> VTy -> VTy -> Tm -> M Tm
coe cxt l sourceTy targetTy m = case (sourceTy, targetTy) of
  (VU i, VU j) | i <= j -> 
    pure $ Code (quoteSize (lvl cxt) j) (Decode (quoteSize (lvl cxt) i) m)

  (VPi n1 a1 b1, VPi n2 a2 b2) -> do
    let cxt' = bind n2 a2 cxt
    let l' = lvl cxt'
    
    u_x <- coe cxt' l' a2 a1 (Var (Ix 0))

    let vu_x = evalTm (env cxt') u_x
    let vm = evalTm (env cxt) m
    let m_u_x = quoteTm l' (vApp vm vu_x)
    
    n_x <- coe cxt' l' (b1 vu_x) (b2 (VVar l)) m_u_x
    
    pure $ Lam n2 n_x

  _ -> 
    if convTy l sourceTy targetTy then pure m 
    else report cxt "Error: Invalid coercion"

elabSize :: Cxt -> RawSize -> M Size
elabSize cxt = \case
  RSzVar x -> do
    let go i [] = report cxt ("Level variable out of scope: " ++ x)
        go i ((x', _):tys)
          | x == x'   = case env cxt !! i of
                          VESize _ -> pure (LVar (Ix i))
                          VETm _ -> report cxt ("Expected a level variable, but '" ++ x ++ "' is a term variable.")
          | otherwise = go (i + 1) tys
    go 0 (types cxt)
  RSz i -> pure (Sz i)
  RSucc s -> Succ <$> elabSize cxt s
  RBig -> pure Big
  ROmega -> pure Omega

checkTy :: Cxt -> Raw -> VSize -> M Ty
checkTy cxt t size = case t of

  RSrcPos pos t -> checkTy (cxt {pos = pos}) t size

  RU s -> do
    s' <- elabSize cxt s
    let vs' = evalSize (env cxt) s'
    if vs' < size
    then pure $ U s'
    else report cxt ("Size issue: U " ++ showSize cxt vs' ++ " is too large to fit in U " ++ showSize cxt size)

  RPi x a b -> do
    a' <- checkTy cxt a size
    let cxt' = bind x (evalTy (env cxt) a') cxt
    b' <- checkTy cxt' b size
    pure $ Pi x a' b'
    
  RLPi l a -> do
    let cxt' = bindLevel l cxt
    a' <- checkTy cxt' a size
    pure $ LPi l a'

  -- mode switch
  _ -> do 
    (tTm, s) <- inferU cxt t
    let vs = evalSize (env cxt) s
    if vs <= size then
      pure (Decode s tTm)
    else report cxt ("Size issue: got a code at level " ++ show s ++ ", but expected at most " ++ show size)

check :: Cxt -> Raw -> VTy -> M Tm
check cxt t a = case (t, a) of
  (RSrcPos pos t, a) -> check (cxt {pos = pos}) t a

  (RLam x t, VPi x' a b) ->
    Lam x <$> check (bind x a cxt) t (b (VVar (lvl cxt)))

  (RLAbs l t, VLPi _ b) -> do
    let cxt' = bindLevel l cxt
    t' <- check cxt' t (b (VLVar (lvl cxt)))
    pure $ LAbs l t'

  (_, VU i) -> do
    u <- checkTy cxt t i
    pure $ Code (quoteSize (lvl cxt) i) u

  (RLet x a t u, a') -> do
    a <- checkTy cxt a VOmega
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
          | x == x'   = case env cxt !! i of
                          VETm _ -> pure (Var (Ix i), a)
                          VESize _ -> report cxt ("Expected a term variable, but '" ++ x ++ "' is a level variable.")
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

  RLApp t s -> do
    (tTm, tTy) <- infer cxt t
    case tTy of
      VLPi _ b -> do
        sz <- elabSize cxt s
        let vsz = evalSize (env cxt) sz
        pure (LApp tTm sz, b vsz)
      _ -> report cxt ("Expected a level-polymorphic type for level application, instead inferred:\n\n  " ++ showVTy cxt tTy)

  RLet x a t u -> do
    a <- checkTy cxt a VOmega
    let ~va = evalTy (env cxt) a
    t <- check cxt t va
    let ~vt = evalTm (env cxt) t
    (u, uty) <- infer (define x vt va cxt) u  
    pure (Let x a t u, uty)


  RU {} -> report cxt "Can't infer type for universe"
  RPi {} -> report cxt "Can't infer type for product type"
  RLam {} -> report cxt "Can't infer type for lambda expression."
  RLPi {} -> report cxt "Can't infer type for level product type"
  RLAbs {} -> report cxt "Can't infer type for level abstraction"


-- printing
--------------------------------------------------------------------------------

fresh :: [Name] -> Name -> Name
fresh ns "_" = "_"
fresh ns x | elem x ns = go (1 :: Int) where
  go n | elem (x ++ show n) ns = go (n + 1)
       | otherwise             = x ++ show n
fresh ns x = x

-- printing precedences
atomp = 3  :: Int -- U, var
appp  = 2  :: Int -- application
pip   = 1  :: Int -- pi
letp  = 0  :: Int -- let, lambda

-- | Wrap in parens if expression precedence is lower than
--   enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

prettySize :: [Name] -> Size -> ShowS
prettySize ns = \case
  LVar (Ix x) -> 
    if x < 0 || x >= length ns then 
      (("l" ++ show x) ++)
    else 
      ((ns !! x) ++)
  Sz i -> (show i ++)
  Succ s -> prettySize ns s . (" + 1"++)
  Big -> ("Tp"++)
  Omega -> ("Omega"++)

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

    App t u                   -> par p appp $ goTm appp ns t . (' ':) . goTm atomp ns u

    Lam (fresh ns -> x) t     -> par p letp $ ("λ "++) . (x++) . goLam (x:ns) t where
                                   goLam ns (Lam (fresh ns -> x) t) =
                                     (' ':) . (x++) . goLam (x:ns) t
                                   goLam ns t =
                                     (". "++) . goTm letp ns t

    LAbs (fresh ns -> x) t    -> par p letp $ ("Λ "++) . (x++) . goLAbs (x:ns) t where
                                   goLAbs ns (LAbs (fresh ns -> x) t') =
                                     (' ':) . (x++) . goLAbs (x:ns) t'
                                   goLAbs ns t' =
                                     (". "++) . goTm letp ns t'

    LApp t s                  -> par p appp $ goTm appp ns t . (" {"++) . prettySize ns s . ("}"++)

    Code i t -> ('[':).prettyTy letp ns t.(']':)

    Let (fresh ns -> x) a t u ->
      par p letp $ ("let "++) . (x++) . (" : "++) . prettyTy letp ns a
      . ("\n    = "++) . goTm letp ns t . ("\n;\n"++) . goTm letp (x:ns) u

prettyTy :: Int -> [Name] -> Ty -> ShowS
prettyTy = goTy where
  piBind ns x a =
    showParen True ((x++) . (" : "++) . goTy letp ns a)

  goTy :: Int -> [Name] -> Ty -> ShowS
  goTy p ns = \case    
    U i                       -> par p appp $ ("U "++).prettySize ns i

    Pi "_" a b                -> par p pip $ goTy appp ns a . (" → "++) . goTy pip ("_":ns) b

    Pi (fresh ns -> x) a b    -> par p pip $ piBind ns x a . goPi (x:ns) b where
                                   goPi ns (Pi "_" a b) = (" → "++) . goTy appp ns a
                                                          . (" → "++) . goTy pip ("_":ns) b
                                   goPi ns (Pi x a b)   = piBind ns x a . goPi (x:ns) b
                                   goPi ns b            = (" → "++) . goTy pip ns b

    LPi (fresh ns -> x) t     -> par p pip $ ("∀ "++) . (x++) . goLPi (x:ns) t where
                                   goLPi ns (LPi (fresh ns -> x) t') =
                                     (' ':) . (x++) . goLPi (x:ns) t'
                                   goLPi ns t' =
                                     (". "++) . goTy pip ns t'

    Decode i t   -> ('<':).prettyTm letp ns t.('>':)

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
keyword x = x `elem` ["let", "λ", "U", "Tp", "Omega", "forall"]

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pRawSizeAtom :: Parser RawSize
pRawSizeAtom = 
      (ROmega <$ pKeyword "Omega")
  <|> (RBig <$ pKeyword "Tp")
  <|> (RSz <$> decimal)
  <|> (RSzVar <$> pIdent)
  <|> parens pRawSize

pRawSize :: Parser RawSize
pRawSize = do
  base <- pRawSizeAtom
  pluses <- many (symbol "+" *> decimal)
  pure $ foldl (\s n -> iterate RSucc s !! n) base pluses

pAtom :: Parser Raw
pAtom =
      withPos (
            (RVar <$> pIdent)
        <|> (RU <$> (pKeyword "U" *> pRawSize))
        <|> (RU RBig <$ pKeyword "Tp")
      )
  <|> parens pRaw

pBinder = pIdent <|> symbol "_"


pSpine :: Parser Raw
pSpine = do
  head <- pAtom
  args <- many (
          (Right <$> try (symbol "{" *> pRawSize <* symbol "}"))
      <|> (Left <$> pAtom)
    )
  pure $ foldl (\t arg -> case arg of Left u -> RApp t u; Right s -> RLApp t s) head args

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

pLPi = do
  symbol "∀" <|> symbol "forall"
  l <- pBinder
  symbol "."
  t <- pRaw
  pure (RLPi l t)

pLLam = do
  symbol "Λ" <|> symbol "/\\"
  l <- pBinder
  symbol "."
  t <- pRaw
  pure (RLAbs l t)

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

pRaw = withPos (pLPi <|> pLLam <|> pLam <|> pLet <|> try pPi <|> funOrSpine)
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