module Parsing where

import Prelude hiding (lookup)
import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Void
import qualified Data.List.NonEmpty as NE
import System.Exit
import Text.Megaparsec

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

import Syntax

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