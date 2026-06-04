
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

type ULvl = Int

data Raw
  = RVar Name              -- x
  | RLam Name Raw          -- \x. t
  | RApp Raw Raw           -- t u
  | RU ULvl                -- U i
  | RPi Name Raw Raw       -- (x : A) -> B
  | RLet Name Raw Raw Raw  -- let x : A = t in u
  | RSrcPos SourcePos Raw  -- source position for error reporting
  deriving Show

-- core syntax
------------------------------------------------------------

data Ty
  = Pi Name ~Ty Ty
    | U ULvl 
    | Decode ULvl Tm

data Tm
  = Var Ix
  | App Tm ~Tm
  | Code Int Ty
  | Lam Name Tm
  | Let Name Ty Tm Tm

-- values
------------------------------------------------------------

type Env = [VTm]

data VTy
  = VPi Name ~VTy (VTm -> VTy)
    | VU Int 
    | VDecode ULvl VTm

data VTm
  = VVar Lvl
  | VApp VTm ~VTm
  | VCode ULvl VTy
  | VLam Name (VTm -> VTm)

--------------------------------------------------------------------------------

evalTm :: Env -> Tm -> VTm
evalTm env = \case
  Var (Ix x)    -> env !! x
  App t u       -> case (evalTm env t, evalTm env u) of
                     (VLam _ t, u) -> t u
                     (t       , u) -> VApp t u
  Lam x t       -> VLam x \v -> evalTm (v:env) t
  Let x _ t u -> evalTm (evalTm env t : env) u

  -- Case of a Coding
  Code i a      -> VCode i (evalTy env a)

evalTy :: Env -> Ty -> VTy
evalTy env = \case
  Pi x a b      -> VPi x (evalTy env a) \v -> evalTy (v:env) b
  U i           -> VU i

  -- Case of a Decoding
  Decode i t    -> case evalTm env t of
    VCode j a | i == j  -> a             -- Beta Rule for the Universe
    v                   -> VDecode i v


lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quoteTm :: Lvl -> VTm -> Tm
quoteTm l = \case
  VVar x      -> Var (lvl2Ix l x)
  VApp t u    -> App (quoteTm l t) (quoteTm l u)
  VLam x t    -> Lam x (quoteTm (l + 1) (t (VVar l)))

  -- Case of a Coding
  VCode i a   -> Code i (quoteTy l a)

quoteTy :: Lvl -> VTy -> Ty
quoteTy l = \case
  VPi  x a b  -> Pi x (quoteTy l a) (quoteTy (l + 1) (b (VVar l)))
  VU i        -> U i

  -- Case of a Decoding
  VDecode i t -> Decode i (quoteTm l t)

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

  (VCode i a, VCode j b) | i == j -> convTy l a b

  _ -> False

convTy :: Lvl -> VTy -> VTy -> Bool
convTy l t u = case (t, u) of
  (VU i, VU i') -> i == i'

  (VPi _ a b, VPi _ a' b') ->
       convTy l a a'
    && convTy (l + 1) (b (VVar l)) (b' (VVar l))

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
  Cxt (VVar l:env) ((x, a):types) (l + 1) pos

-- Extend Cxt with a definition
define :: Name -> VTm -> VTy -> Cxt -> Cxt
define x ~t ~a (Cxt env types l pos) =
  Cxt (t:env) ((x, a):types) (l + 1) pos

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

--------------------------------------------------------------------------------

vApp :: VTm -> VTm -> VTm
vApp (VLam _ f) v = f v
vApp f          v = VApp f v

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

    let vu_x = evalTm (env cxt') u_x
    let vm = evalTm (env cxt) m
    let m_u_x = quoteTm l' (vApp vm vu_x)
    
    n_x <- coe cxt' l' (b1 vu_x) (b2 (VVar l)) m_u_x
    
    pure $ Lam n2 n_x

  _ -> 
    if convTy l sourceTy targetTy then pure m 
    else report cxt "Error: Invalid coercion"

checkTy :: Cxt -> Raw -> Maybe ULvl -> M Ty
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

-- printing precedences
atomp = 3  :: Int -- U, var
appp  = 2  :: Int -- application
pip   = 1  :: Int -- pi
letp  = 0  :: Int -- let, lambda

-- | Wrap in parens if expression precedence is lower than
--   enclosing expression precedence.
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

    App t u                   -> par p appp $ goTm appp ns t . (' ':) . goTm atomp ns u

    Lam (fresh ns -> x) t     -> par p letp $ ("λ "++) . (x++) . goLam (x:ns) t where
                                   goLam ns (Lam (fresh ns -> x) t) =
                                     (' ':) . (x++) . goLam (x:ns) t
                                   goLam ns t =
                                     (". "++) . goTm letp ns t

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
    U i                       -> par p appp $ ("U "++).(show i++)

    Pi "_" a b                -> par p pip $ goTy appp ns a . (" → "++) . goTy pip ("_":ns) b

    Pi (fresh ns -> x) a b    -> par p pip $ piBind ns x a . goPi (x:ns) b where
                                   goPi ns (Pi "_" a b) = (" → "++) . goTy appp ns a
                                                          . (" → "++) . goTy pip ("_":ns) b
                                   goPi ns (Pi x a b)   = piBind ns x a . goPi (x:ns) b
                                   goPi ns b            = (" → "++) . goTy pip ns b

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
keyword x = x == "let" || x == "λ" || x == "U" 

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

pRaw = withPos (pLam <|> pLet <|> try pPi <|> funOrSpine)
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