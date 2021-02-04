{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.NonParametrized.MCoxeter where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.PathGroupoid

open import Pi+.Misc
open import Pi+.Common.Arithmetic
open import Pi+.Common.ListN
open import Pi+.Coxeter.NonParametrized.ReductionRel
open import Pi+.Coxeter.NonParametrized.Diamond

open ≅*-Reasoning


data _↔_ : Listℕ -> Listℕ -> Set where
  MC : {m1 m2 mf : Listℕ} -> (p1 : m1 ≅* mf) -> (p2 : m2 ≅* mf) -> m1 ↔ m2

refl↔ : (m : Listℕ) -> (m ↔ m)
refl↔ m = MC idp idp

comm↔ : (m1 m2 : Listℕ) -> (m1 ↔ m2) -> (m2 ↔ m1)
comm↔ m1 m2 (MC p1 p2) = MC p2 p1

trans↔ : (m1 m2 m3 : Listℕ) -> (r1 : m1 ↔ m2) -> (r2 : m2 ↔ m3) -> (m1 ↔ m3)
trans↔ m1 m2 m3 (MC p1 p2) (MC p3 p4) =
  let lemma-m , lemma1 , lemma2 = diamond-full p2 p3
  in  MC (trans p1 lemma1) (trans p4 lemma2)