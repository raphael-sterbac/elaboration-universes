module Syntax where

import Prelude hiding (lookup)
import Data.List.NonEmpty (NonEmpty)
import Text.Megaparsec

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
  | RFst Raw
  | RSnd Raw
  | RLet Name Raw Raw Raw
  | RSrcPos SourcePos Raw
  | RData Name [(Name, Raw)] Raw (NonEmpty (Name, Raw)) Raw
  | RAt Raw Size
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

deriving instance Show Tm
deriving instance Show Ty
deriving instance Show Label
deriving instance Show Desc
