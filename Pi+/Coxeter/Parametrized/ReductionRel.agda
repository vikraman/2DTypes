{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Parametrized.ReductionRel where

open import lib.Base
open import lib.Relation
open import lib.NType
open import lib.types.SetQuotient public
open import lib.types.List
open import lib.types.Fin

open import Pi+.Misc
open import Pi+.Coxeter.Common.Arithmetic
open import Pi+.Coxeter.Common.ListN
open import Pi+.Coxeter.Common.LList


syntax ReductionRel n x y = x ≅[ n ] y

↓N : {m : ℕ} -> (a b : Fin m) -> LList m
↓N = ?

data ReductionRel : (m : ℕ) -> (l : LList m) -> (r : LList m) -> Type₀ where
  cancel≅ : {m : ℕ} -> (l : LList m) -> (r : LList m) -> (n : (Fin m)) -> (l +++ (n :: n :: r)) ≅[ m ] (l +++ r)
  swap≅ : {m : ℕ} -> (l : LList m) -> (r : LList m) -> (n k : (Fin m)) -> (S (k .fst) < (n .fst)) -> (l +++ n :: k :: r) ≅[ m ] l +++ k :: n :: r
--   long≅ : {m : ℕ} -> (l : LList m) -> (r : LList m) -> (n k : (Fin m)) -> l +++ (n ↓ (2 + k)) +++ (1 + k + n) :: r) ≅[ m ] l +++ (k + n) :: (n ↓ (2 + k)) +++ r

syntax ReductionRel* n x y = x ≅*[ n ] y

data ReductionRel* : (m : ℕ) -> (l : LList m) -> (r : LList m) -> Type₀ where
  idp : {m : ℕ} (l : LList m) -> l ≅*[ m ] l
  trans≅ : {m : ℕ} {l1 l2 l3 : LList m} -> (l1 ≅[ m ] l2) -> (l2 ≅*[ m ] l3) -> l1 ≅*[ m ] l3

-- small-reductions : {n : ℕ} -> (m mf : LList n) -> ((m .fst) ≅* (mf .fst)) -> (m ≅*[ n ] mf)
-- small-reductions = ?

-- {-# NON_TERMINATING #-}
-- LList-to-LehmerProper : {n : ℕ} -> (m : LList n) -> Σ _ (λ nf -> (n ≤ nf) × Σ _ (λ cl -> rev (m .fst) ≅* immersionProper {nf} cl))
-- LList-to-LehmerProper {n} m = 
--   let rn , rcl = Listℕ-to-LehmerProper (m .fst)
--   in {!   !}
