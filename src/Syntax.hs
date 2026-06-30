{-# LANGUAGE InstanceSigs #-}
module Syntax where

import Prelude hiding (lookup)
import Data.List.NonEmpty (NonEmpty)
import Text.Megaparsec

-- De Bruijn index.
newtype Ix  = Ix  Int deriving (Eq, Show, Num) via Int

-- De Bruijn level.
newtype Lvl = Lvl Int deriving (Eq, Show, Num) via Int

data RawSize = RSzVar Name | RSz Int | RSucc RawSize | RBig | ROmega deriving Show
data Size = LVar Ix | Sz Int | Succ Size | Big | Omega 

data SizeFlattened = FZero Int | FVar Ix Int | FBig | FOmega deriving (Eq)

viewSize :: Size -> SizeFlattened
viewSize (Sz i) = FZero i
viewSize (LVar x) = FVar x 0
viewSize Big = FBig
viewSize Omega = FOmega
viewSize (Succ s) = case viewSize s of
  FZero n -> FZero (n + 1)
  FVar x n -> FVar x (n + 1)
  FBig -> FBig     
  FOmega -> FOmega  

instance Eq Size where
  (==) :: Size -> Size -> Bool
  s1 == s2 = viewSize s1 == viewSize s2

instance Ord Size where
  s1 <= s2 = case (viewSize s1, viewSize s2) of
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

type Name = String

data Raw
  = RVar Name
  | RLam Name Raw
  | RApp Raw Raw
  | RU RawSize
  | RPi Name Raw Raw
  | RLPi Name Raw
  | RLAbs Name Raw
  | RLApp Raw RawSize
  | RPair Raw Raw
  | ROne
  | RFst Raw
  | RSnd Raw
  | RLet Name Raw Raw Raw
  | RSrcPos SourcePos Raw
  | RData Name [(Name, Raw)] Raw (NonEmpty (Name, Raw)) Raw
  | RRecord [(Name, Raw)]
  | RRecordVal [(Name, Raw)]
  | RProj Raw Name
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
  | LPi Name Ty
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
  | LAbs Name Tm
  | LApp Tm Size 
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

deriving instance Show Tm
deriving instance Show Ty
deriving instance Show Label
deriving instance Show Desc
