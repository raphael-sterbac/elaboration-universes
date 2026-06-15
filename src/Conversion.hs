module Conversion where

import Prelude hiding (lookup)

import Syntax
import Evaluation

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