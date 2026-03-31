module Main where

import Control.Applicative hiding (many, some)
import Control.Exception hiding (try)
import Control.Monad
import Data.Char
import Data.IORef
import Data.Void
import System.Environment
import System.Exit
import System.IO.Unsafe
import Text.Megaparsec
import Text.Printf

import qualified Data.IntMap                as IM
import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L
-- import Debug.Trace

-- examples
--------------------------------------------------------------------------------

ex0 = main' "nf" $ unlines [

  "let f : U 1 -> U 1 = \\A. A;",
  "let g : U 0 -> U 2 = f;",
  "let f : (A : U 0) -> A -> A = \\A x. x;",
  "let u : U 3 = U 0;",

  "let IdTy1    : U 2 =  ((A : U 1) -> A -> A);",
  "let ConstTy0 : U 1 =  ((A B : U 0) -> A -> B -> A);",
  "let id1 : IdTy1 = \\A x. x;",
  "let const0 : ConstTy0 = \\A B x y. x;",
  "let foo : ConstTy0 = id1 ConstTy0 const0;",

  "let Nat  : U 1 =  ((N : U 0) -> ( N -> N) -> N -> N) ;",
  "let zero : Nat = λ N s z. z;",
  "let one  : Nat = λ N s z. s z;",
  "let five : Nat = \\N s z. s (s (s (s (s z)))) ;",
  "let add  : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z) ;",
  "let mul  : Nat -> Nat -> Nat = \\a b N s z. a N (b N s) z ;",
  "let ten      : Nat = add five five ;",
  "let hundred  : Nat = mul ten ten ;",

  "let Eq1 : (A : U 1) → A → A → U 1",
  "    = λ A x y.  ((P : A → U 0) → (P x) → (P y) );",

  "let refl1 : (A : U 1)(x : A) → Eq1 A x x",
  "  = λ A x P px. px;",

  "let p1 : Eq1 Nat ten ten = refl1 Nat ten;",
  "id1 Nat hundred"

  ]



-- Metacontext
--------------------------------------------------------------------------------

newtype MetaVar = MetaVar {unMetaVar :: Int} deriving (Eq, Show, Num) via Int

data MetaEntry = Solved Val | Unsolved

nextMeta :: IORef Int
nextMeta = unsafeDupablePerformIO $ newIORef 0    -- alternative: ReaderT IO (reader has metacontext)
{-# noinline nextMeta #-}

mcxt :: IORef (IM.IntMap MetaEntry)               -- in "production", we'd have mutable array instead of IntMap
mcxt = unsafeDupablePerformIO $ newIORef mempty
{-# noinline mcxt #-}

lookupMeta :: MetaVar -> MetaEntry
lookupMeta (MetaVar m) = unsafeDupablePerformIO $ do
  ms <- readIORef mcxt
  case IM.lookup m ms of
    Just e  -> pure e
    Nothing -> error "impossible"

reset :: IO ()
reset = do
  writeIORef nextMeta 0
  writeIORef mcxt mempty

-- Snoc
--------------------------------------------------------------------------------

infixl 4 :>
pattern xs :> x <- x:xs where (:>) xs ~x = x:xs
{-# complete (:>), [] #-}


-- syntax
--------------------------------------------------------------------------------

-- | De Bruijn index.
newtype Ix  = Ix {unIx :: Int} deriving (Eq, Show, Num) via Int

-- | De Bruijn level.
newtype Lvl = Lvl {unLvl :: Int} deriving (Eq, Ord, Show, Num) via Int


type Name = String

data Raw
  = RVar Name              -- x
  | RLam Name Raw          -- \x. t
  | RApp Raw Raw           -- t u
  | RU Int                 -- U i
  | RPi Name Raw Raw       -- (x : A) -> B
  | RLet Name Raw Raw Raw  -- let x : A = t in u
  | RSrcPos SourcePos Raw  -- source position for error reporting
  | RHole                  -- _
  deriving Show

-- core syntax
------------------------------------------------------------

data BD = Bound | Defined
  deriving Show


data Ty
  = Pi Name ~Ty Ty
  | U Int 
  | Decode Int Tm
  
data Tm
  = Var Ix
  | App Tm ~Tm
  | Code Int Ty
  | Lam Name Tm
  | Let Name Ty Tm Tm
  | Meta MetaVar
  | InsertedMeta MetaVar [BD]

-- values
------------------------------------------------------------

type Env = [Val]
type Spine   = [Val]
data Closure = ClosureTm Env Tm | ClosureTy Env Ty


data VTy
  = VPi Name ~VTy {-# unpack #-} ClosureTy
    | VU Int 
    | VDecode Int Val

data Val
  = VFlex MetaVar Spine
  | VRigid Lvl Spine
  | VApp Val ~Val
  | VCode Int VTy
  | VLam Name {-# unpack #-} ClosureTm

pattern VVar  x = VRigid x []
pattern VMeta m = VFlex m []

infixl 8 $$
($$) :: ClosureTm -> Val -> Val
($$) (ClosureTm env t) ~u = evalTm (env :> u) t

infixl 9 $$
($$) :: ClosureTy -> Val -> Val
($$) (ClosureTy env t) ~u = evalTm (env :> u) t

--------------------------------------------------------------------------------

vDecode :: Int -> Val -> VTy
vDecode i = \case
  VCode j a | i == j  -> a
  v                   -> VDecode i v

vApp :: Val -> Val -> Val
vApp t ~u = case t of
  VLam _ t    -> t $$ u
  VFlex  m sp -> VFlex m (sp :> u)  -- add the argument to the spine
  VRigid x sp -> VRigid x (sp :> u) -- add the argument to the spine
  _           -> error "impossible"

-- Apply single value to multiple variables
vAppSp :: Val -> Spine -> Val
vAppSp t = \case
  []      -> t
  sp :> u -> vAppSp t sp `vApp` u

vMeta :: MetaVar -> Val
vMeta m = case lookupMeta m of
  Solved v -> v
  Unsolved -> VMeta m

-- We apply a value to a mask of entries from the environment.
vAppBDs :: Env -> Val -> [BD] -> Val
vAppBDs env ~v bds = case (env, bds) of
  ([]       , []            ) -> v
  (env :> t , bds :> Bound  ) -> vAppBDs env v bds `vApp` t
  (env :> t , bds :> Defined) -> vAppBDs env v bds
  _                           -> error "impossible"


evalTm :: Env -> Tm -> Val
evalTm env = \case
  Var (Ix x)    -> env !! x
  App t u       -> vApp (evalTm env t) (evalTm env u)
  Lam x t            -> VLam x (Closure env t)
  Code i a      -> VCode i (evalTy env a)
  Let x _ t u -> evalTm (evalTm env t : env) u
  Meta m             -> vMeta m
  InsertedMeta m bds -> vAppBDs env (vMeta m) bds

evalTy :: Env -> Ty -> VTy
evalTy env = \case
  Pi x a b           -> VPi x (evalTy env a) (Closure env b)
  U i           -> VU i
  Decode i t    -> vDecode i (evalTm env t)

force :: Val -> Val
force = \case
  VFlex m sp | Solved t <- lookupMeta m -> force (vAppSp t sp)
  t -> t

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quoteSp :: Lvl -> Tm -> Spine -> Tm
quoteSp l t = \case
  []      -> t
  sp :> u -> App (quoteSp l t sp) (quoteTm l u)

quoteTm :: Lvl -> Val -> Tm
quoteTm l = \case
  VVar x      -> Var (lvl2Ix l x)
  VApp t u    -> App (quoteTm l t) (quoteTm l u)
  VLam x t    -> Lam x (quoteTm (l + 1) (t $$ VVar l))
  VCode i a   -> Code i (quoteTy l a)
  VFlex m sp  -> quoteSp l (Meta m) sp
  VRigid x sp -> quoteSp l (Var (lvl2Ix l x)) sp

quoteTy :: Lvl -> VTy -> Ty
quoteTy l = \case
  VPi  x a b  -> Pi x (quoteTy l a) (quoteTy (l + 1) (b $$ VVar l))
  VU i        -> U i
  VDecode i t -> Decode i (quoteTm l t)

nf :: Env -> Tm -> Tm
nf env t = quoteTm (Lvl (length env)) (evalTm env t)


-- Metavariables and pattern unification
--------------------------------------------------------------------------------

freshMeta :: Cxt -> IO Tm
freshMeta cxt = do
  m <- readIORef nextMeta
  writeIORef nextMeta $! (m + 1)             -- increment nextMeta
  modifyIORef' mcxt $ IM.insert m Unsolved   -- add a new unsolved metaEntry
  pure $ InsertedMeta (MetaVar m) (bds cxt)  -- as I previously mentioned, we just drop the [BD] here
                                             -- Cxt has a (bds :: Cxt -> [BD]) field

-- partial renaming from Γ to Δ
data PartialRenaming = PRen {
    dom :: Lvl                -- size of Γ
  , cod :: Lvl                -- size of Δ
  , ren :: IM.IntMap Lvl }    -- mapping from Δ vars to Γ vars

-- Lifting a partial renaming over an extra bound variable.
-- Given (σ : PRen Γ Δ), (lift σ : PRen (Γ, x : A[σ]) (Δ, x : A))
lift :: PartialRenaming -> PartialRenaming
lift (PRen dom cod ren) =
  PRen (dom + 1) (cod + 1) (IM.insert (unLvl cod) dom ren)


--  invert : (Γ : Cxt) → (spine : Sub Γ Δ) → PRen Δ Γ
invert :: Lvl -> Spine -> IO PartialRenaming
invert gamma sp = do

  let go :: Spine -> IO (Lvl, IM.IntMap Lvl)
      go []        = pure (0, mempty)
      go (sp :> t) = do
        (dom, ren) <- go sp
        case force t of
          VVar (Lvl x) | IM.notMember x ren -> pure (dom + 1, IM.insert x dom ren)
          _                                 -> throwIO UnifyError

  (dom, ren) <- go sp
  pure $ PRen dom gamma ren

-- perform the partial renaming on rhs, while also checking for "m" occurrences.
rename :: MetaVar -> PartialRenaming -> Val -> IO Tm
rename m pren v = go pren v where

  goSp :: PartialRenaming -> Tm -> Spine -> IO Tm
  goSp pren t []        = pure t
  goSp pren t (sp :> u) = App <$> goSp pren t sp <*> go pren u

  go :: PartialRenaming -> Val -> IO Tm
  go pren t = case force t of
    VFlex m' sp | m == m'   -> throwIO UnifyError -- occurs check
                | otherwise -> goSp pren (Meta m') sp

    VRigid (Lvl x) sp -> case IM.lookup x (ren pren) of
      Nothing -> throwIO UnifyError  -- scope error ("escaping variable" error)
      Just x' -> goSp pren (Var $ lvl2Ix (dom pren) x') sp

    VLam x t  -> Lam x <$> go (lift pren) (t $$ VVar (cod pren))
    -- TODO : add other cases


{-
Wrap a term in lambdas.
-}
lams :: Lvl -> Tm -> Tm
lams l = go 0 where
  go x t | x == l = t
  go x t = Lam ("x"++show (x+1)) $ go (x + 1) t

--       Γ      ?α         sp       rhs
solve :: Lvl -> MetaVar -> Spine -> Val -> IO ()
solve gamma m sp rhs = do
  pren <- invert gamma sp
  rhs  <- rename m pren rhs
  let solution = eval [] $ lams (dom pren) rhs
  modifyIORef' mcxt $ IM.insert (unMetaVar m) (Solved solution)


{-
The actual unification algorithm is fairly simple, it works in a structural
fashion, like conversion checking before.  The main complication, as we've seen,
is the pattern unification case.
-}

unifySp :: Lvl -> Spine -> Spine -> IO ()
unifySp l sp sp' = case (sp, sp') of
  ([]     , []       ) -> pure ()
  (sp :> t, sp' :> t') -> unifySp l sp sp' >> unify l t t'
  _                    -> throwIO UnifyError -- rigid mismatch error

unify :: Lvl -> Val -> Val -> IO ()
unify l t u = case (force t, force u) of
  (VLam _ t   , VLam _ t'    ) -> unify (l + 1) (t $$ VVar l) (t' $$ VVar l)
  (t          , VLam _ t'    ) -> unify (l + 1) (t `vApp` VVar l) (t' $$ VVar l)
  (VLam _ t   , t'           ) -> unify (l + 1) (t $$ VVar l) (t' `vApp` VVar l)

  (VRigid x sp, VRigid x' sp') | x == x' -> unifySp l sp sp'
  (VFlex m sp , VFlex m' sp' ) | m == m' -> unifySp l sp sp'

  (VFlex m sp , t'           ) -> solve l m sp t'
  (t          , VFlex m' sp' ) -> solve l m' sp' t
  _                            -> throwIO UnifyError  -- rigid mismatch error

-- Elaboration
--------------------------------------------------------------------------------

-- type of every variable in scope
type Types = [(Name, VTy)]

-- | Elaboration context.
data Cxt = Cxt {env :: Env, types :: Types, lvl :: Lvl, pos :: SourcePos}
   -- "unzipped" Cxt definition, for performance reason (also for convenience)

emptyCxt :: SourcePos -> Cxt
emptyCxt = Cxt [] [] 0

-- | Extend Cxt with a bound variable.
bind :: Name -> VTy -> Cxt -> Cxt
bind x ~a (Cxt env types l pos) =
  Cxt (VVar l:env) ((x, a):types) (l + 1) pos

-- | Extend Cxt with a definition.
define :: Name -> Val -> VTy -> Cxt -> Cxt
define x ~t ~a (Cxt env types l pos) =
  Cxt (t:env) ((x, a):types) (l + 1) pos

-- | Typechecking monad. We annotate the error with the current source position.
type M = Either (String, SourcePos)

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

showVal :: Cxt -> Val -> String
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


cast :: Cxt -> Lvl -> VTy -> VTy -> Tm -> M Tm
cast cxt l sourceTy targetTy m =
  if convTy l sourceTy targetTy then
    pure m 
  else case (sourceTy, targetTy) of
  
  (VU i, VU j) | i + 1 <= j -> 
    pure $ Code j (Decode i m)

  (VPi n1 a1 b1, VPi n2 a2 b2) -> do
    let cxt' = bind n2 a2 cxt
    let l' = lvl cxt'
    
    u_x <- cast cxt' l' a2 a1 (Var (Ix 0))

    let env' = env cxt'
    let vu_x = evalTm env' u_x
    
    let vm = evalTm (env cxt) m
    let vApp = case vm of
                 VLam _ f -> f vu_x
                 _        -> VApp vm vu_x
                 
    let m_u_x = quoteTm l' vApp
    
    n_x <- cast cxt' l' (b1 vu_x) (b2 (VVar l)) m_u_x
    
    pure $ Lam n2 n_x

  _ -> report cxt ("Invalid cast : " ++ showVTy cxt sourceTy ++ " to " ++ showVTy cxt targetTy)

checkTy :: Cxt -> Raw -> Maybe Int -> M Ty
checkTy cxt t size = case t of
  RSrcPos pos t -> checkTy (cxt {pos = pos}) t size

  RU i -> case size of 
    Nothing -> pure $ U i
    Just j | i <= j -> pure $ U i
    Just k -> report cxt ("Size issue: U " ++ show i ++ ", but expected a universe in U " ++ show k)

  RPi x a b -> do
    a' <- checkTy cxt a size
    let cxt' = bind x (evalTy (env cxt) a') cxt
    b' <- checkTy cxt' b size
    pure $ Pi x a' b'

  RVar x -> do
    (t, j) <- inferU cxt t
    case size of 
      Nothing -> pure $ Decode j t
      Just k -> pure $ Decode j t
  
  RApp t u -> do
    (t_tm, t_ty) <- infer cxt t
    case t_ty of
      VPi _ a b -> do
        u_tm <- check cxt u a
        let v_u = evalTm (env cxt) u_tm
        case b v_u of
          VU i -> case size of 
            Nothing -> pure $ Decode i (App t_tm u_tm)
            Just k -> pure $ Decode i (App t_tm u_tm)
          _ -> report cxt "Expected a universe in the codomain of the application"
          
      _ -> report cxt $ "Expected a function type, instead inferred:\n\n  " ++ showVTy cxt t_ty

  _ -> report cxt "Failure"


check :: Cxt -> Raw -> VTy -> M Tm
check cxt t a = case (t, a) of
  (RSrcPos pos t, a) -> check (cxt {pos = pos}) t a

  (RLam x t, VPi x' a b) ->
    Lam x <$> check (bind x a cxt) t (b (VVar (lvl cxt)))

  (RU i, VU j) -> do
    u <- checkTy cxt (RU i) (Just j)
    pure $ Code j u

  (RPi x a b, VU i) -> do
    a' <- checkTy cxt a (Just i)
    let cxt' = bind x (evalTy (env cxt) a') cxt
    b' <- checkTy cxt' b (Just i)
    pure $ Code i (Pi x a' b')


  (RLet x a t u, a') -> do
    a <- checkTy cxt a Nothing
    let ~va = evalTy (env cxt) a
    t <- check cxt t va
    let ~vt = evalTm (env cxt) t
    u <- check (define x vt va cxt) u a' 
    pure (Let x a t u)

  -- mode switch : conversion
  _ -> do
    (m, bTy) <- infer cxt t
    cast cxt (lvl cxt) bTy a m

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
          putStrLn $ showTm0 $ nf0 t
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