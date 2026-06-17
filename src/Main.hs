module Main where

import Prelude hiding (lookup)
import System.Environment (getArgs)
import Text.Megaparsec
import Text.Printf
import System.Exit (exitFailure, exitSuccess)

import Evaluation
import Elaboration
import Parsing

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
        Left e -> do
          putStrLn $ errorBundlePretty e
          exitFailure  
        Right tm -> do
          
          let cxt = emptyCxt (initialPos filepath)
          case infer cxt tm of
            Left err -> do 
              displayError src err
              exitFailure 
            Right (t, a) -> case mode of
              "nf" -> do
                putStrLn $ showTm0 $ nf [] t
                putStrLn "  :"
                putStrLn $ showTy0 $ quoteTy 0 a
                exitSuccess
              "elab" -> putStrLn $ showTm0 $ t
              "type" -> putStrLn $ showTy0 $ quoteTy 0 a
              _      -> pure ()
              
    _ -> putStrLn helpMsg