{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Parametrized.Coxeter where

open import lib.Base
open import lib.types.Nat using (_+_; <-ap-S; _<_; _≤_)
open import lib.NType
open import lib.PathGroupoid
open import lib.types.Fin
open import lib.types.List
open import Pi+.Extra

⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
⟨_⟩ = Fin-S

S⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
S⟨ k , kltn ⟩ = S k , <-ap-S kltn

data _≈_ {m : ℕ} : List (Fin (S m)) → List (Fin (S m)) → Type₀ where
    cancel : {n : Fin (S m)} {w : List (Fin (S m))} → (n :: n :: w) ≈ w
    swap : {n : Fin (S m)} {k : Fin (S m)} → (S (k .fst) < (n .fst)) → {w : List (Fin (S m))} → (n :: k :: w) ≈ (k :: n :: w)
    braid : {n : Fin m} {w : List (Fin (S m))} → (S⟨ n ⟩ :: ⟨ n ⟩ :: S⟨ n ⟩ :: w) ≈ (⟨ n ⟩ :: S⟨ n ⟩ :: ⟨ n ⟩ :: w)

    idp : {l : List (Fin (S m))} -> l ≈ l
    comm : {l1 l2 : List (Fin (S m))} -> (l1 ≈ l2) -> l2 ≈ l1
    trans : {l1 l2 l3 : List (Fin (S m))} -> (l1 ≈ l2) -> (l2 ≈ l3) -> l1 ≈ l3

    respects-:: : {l l' : List (Fin (S m))} -> (l ≈ l') -> (n : Fin (S m)) -> n :: l ≈ n :: l'
