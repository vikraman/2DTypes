{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.NonParametrized.Coxeter where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.PathGroupoid
open import lib.types.Fin

open import Pi+.Misc
open import Pi+.Coxeter.Common.Arithmetic
open import Pi+.Coxeter.Common.ListN
open import Pi+.Coxeter.NonParametrized.ReductionRel
open import Pi+.Coxeter.NonParametrized.MCoxeter
open import Pi+.Coxeter.NonParametrized.MCoxeterS
open import Pi+.Coxeter.NonParametrized.Diamond

data _~_ : Listℕ -> Listℕ -> Set where
  cancel~ : {n : ℕ} -> (n ∷ n ∷ nil) ~ nil
  swap~ : {n : ℕ} -> {k : ℕ} -> (S k < n) -> (n ∷ k ∷ nil) ~ (k ∷ n ∷ nil)
  braid~ : {n : ℕ} -> ((S n) ∷ n ∷ (S n) ∷ nil) ~ (n ∷ (S n) ∷ n ∷ nil)
  respects-l~ : (l : Listℕ) -> {r r' lr lr' : Listℕ} -> (r ~ r') -> (lr == l ++ r) -> (lr' == l ++ r') -> lr ~ lr'
  respects-r~ : {l l' : Listℕ} -> (r : Listℕ) ->{lr l'r : Listℕ} -> (l ~ l') -> (lr == l ++ r) -> (l'r == l' ++ r) -> lr ~ l'r
  idp~ : {m : Listℕ} -> m ~ m
  comm~ : {m1 m2 : Listℕ} -> (m1 ~ m2) -> m2 ~ m1
  trans~ : {m1 m2 m3 : Listℕ} -> (m1 ~ m2) -> (m2 ~ m3) -> m1 ~ m3
