{-# OPTIONS --without-K --rewriting #-}

module Pi+.Common.FinHelpers where

open import lib.Base
open import lib.types.Nat
open import lib.types.Fin
open import lib.PathGroupoid
open import lib.NType
open import Pi+.Misc

⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
⟨_⟩ = Fin-S

S⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
S⟨ k , kltn ⟩ = S k , <-ap-S kltn

_≤^_ : {m : ℕ} -> Fin m -> Fin m -> Type₀
k ≤^ n = (k .fst) < S (n .fst)

<-down : {n k : ℕ} -> (S n < k) -> (n < k)
<-down p = <-cancel-S (ltSR p)
