{-# OPTIONS --without-K --rewriting #-}

module Pi+.CoxeterCommon.LList where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.NType
open import lib.PathGroupoid

open import Pi+.CoxeterCommon.Arithmetic
open import Pi+.CoxeterCommon.Lists


data _>>_ : ℕ -> List -> Type₀ where
  nil : {n : ℕ} -> n >> nil
  _:⟨_⟩:_ : {n : ℕ} -> {l : List} -> (k : ℕ) -> (k < n) -> n >> l -> n >> (k :: l)

extract-proof : {n : ℕ} -> {l : List} -> {a : ℕ} -> (n >> (a :: l)) -> (a < n)
extract-proof (_ :⟨ p ⟩: _) = p

>>-↓ : (n k r : ℕ) -> (r + k ≤ n) -> (n >> (k ↓ r))
>>-↓ n k 0 p = nil
>>-↓ n k (S r) p = (r + k) :⟨ p ⟩: (>>-↓ n k r (≤-down p))

>>-++ : {n : ℕ} -> {l1 l2 : List} -> n >> l1 -> n >> l2 -> n >> (l1 ++ l2)
>>-++ {n} {nil} {l2} ll1 ll2 = ll2
>>-++ {n} {x :: l1} {l2} (.x :⟨ p ⟩: ll1) ll2 = x :⟨ p ⟩: (>>-++ ll1 ll2)

>>-S : {n : ℕ} -> {l : List} -> (n >> l) -> ((S n) >> l)
>>-S  nil = nil
>>-S  (k :⟨ p ⟩: l') = k :⟨ ≤-up p ⟩: >>-S l'

LList : ℕ → Type₀
LList n = Σ _ (λ l → n >> l)