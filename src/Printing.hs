module Printing where

import Prelude hiding (lookup)

import Syntax
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
  isRecordVal :: Tm -> Bool
  isRecordVal One = True
  isRecordVal (DPair _ _ u) = isRecordVal u
  isRecordVal _ = False

  printRecordVal :: [Name] -> Tm -> ShowS
  printRecordVal ns (DPair x t u) = 
    (x++) . (" = "++) . goTm letp ns t .
    (case u of
      One -> id
      _   -> (", "++) . printRecordVal ns u)
  printRecordVal _ _ = id

  goTm :: Int -> [Name] -> Tm -> ShowS
  goTm p ns = \case
    tm@(DPair _ _ _) | isRecordVal tm -> par p appp $ ("{ "++) . printRecordVal ns tm . (" }"++)
    
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
  
  isRecord :: Ty -> Bool
  isRecord Unit = True
  isRecord (Sigma _ _ b) = isRecord b
  isRecord _ = False

  printRecord :: [Name] -> Ty -> ShowS
  printRecord ns (Sigma (fresh ns -> x) a b) = 
    (x++) . (" : "++) . goTy letp ns a . 
    (case b of
      Unit -> id
      _    -> (", "++) . printRecord (x:ns) b)
  printRecord _ _ = id

  goTy :: Int -> [Name] -> Ty -> ShowS
  goTy p ns = \case    
    ty@(Sigma _ _ _) | isRecord ty -> par p appp $ ("{ "++) . printRecord ns ty . (" }"++)
       
    U Big -> ("Tp"++)
    U i -> par p appp $ ("U "++).(show i++)

    Pi "_" a b -> par p pip $ goTy appp ns a . (" → "++) . goTy pip ("_":ns) b

    Pi (fresh ns -> x) a b -> par p pip $ ("Π "++) . piBind ns x a . goPi (x:ns) b where
      goPi ns (Pi "_" a b) = (". "++) . goTy appp ns a . (" → "++) . goTy pip ("_":ns) b
      goPi ns (Pi x a b) = piBind ns x a . goPi (x:ns) b
      goPi ns b = (". "++) . goTy pip ns b

    Decode i t -> ('<':).prettyTm letp ns t.('>':)

    Unit -> ("{}"++)

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
