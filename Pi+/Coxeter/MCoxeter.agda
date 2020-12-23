{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.MCoxeter where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.PathGroupoid

open import Pi+.Misc
open import Pi+.Coxeter.Arithmetic
open import Pi+.Coxeter.Lists
open import Pi+.Coxeter.ReductionRel
open import Pi+.Coxeter.Diamond

open ≅*-Reasoning


data _≃_ : List -> List -> Set where
  comm≅ : {m1 m2 mf : List} -> (p1 : m1 ≅* mf) -> (p2 : m2 ≅* mf) -> m1 ≃ m2

refl≃ : (m : List) -> (m ≃ m)
refl≃ m = comm≅ idp idp

comm≃ : (m1 m2 : List) -> (m1 ≃ m2) -> (m2 ≃ m1)
comm≃ m1 m2 (comm≅ p1 p2) = comm≅ p2 p1

trans≃ : (m1 m2 m3 : List) -> (r1 : m1 ≃ m2) -> (r2 : m2 ≃ m3) -> (m1 ≃ m3)
trans≃ m1 m2 m3 (comm≅ p1 p2) (comm≅ p3 p4) =
  let lemma-m , lemma1 , lemma2 = diamond-full p2 p3
  in  comm≅ (trans p1 lemma1) (trans p4 lemma2)