{-# OPTIONS --without-K --rewriting #-}

module Pi+.CoxeterNonParametrized.MCoxeter where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.PathGroupoid

open import Pi+.Misc
open import Pi+.CoxeterCommon.Arithmetic
open import Pi+.CoxeterCommon.Lists
open import Pi+.CoxeterNonParametrized.ReductionRel
open import Pi+.CoxeterNonParametrized.Diamond

open ≅*-Reasoning


data _↔_ : List -> List -> Set where
  MC : {m1 m2 mf : List} -> (p1 : m1 ≅* mf) -> (p2 : m2 ≅* mf) -> m1 ↔ m2

refl↔ : (m : List) -> (m ↔ m)
refl↔ m = MC idp idp

comm↔ : (m1 m2 : List) -> (m1 ↔ m2) -> (m2 ↔ m1)
comm↔ m1 m2 (MC p1 p2) = MC p2 p1

trans↔ : (m1 m2 m3 : List) -> (r1 : m1 ↔ m2) -> (r2 : m2 ↔ m3) -> (m1 ↔ m3)
trans↔ m1 m2 m3 (MC p1 p2) (MC p3 p4) =
  let lemma-m , lemma1 , lemma2 = diamond-full p2 p3
  in  MC (trans p1 lemma1) (trans p4 lemma2)