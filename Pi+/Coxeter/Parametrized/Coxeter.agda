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

-- This is the one that is to be used with HIT
-- data _≈₀_ {m : ℕ} : List (Fin (S m)) → List (Fin (S m)) → Type₀ where
--     cancel : {n : Fin (S m)} {w : List (Fin (S m))} → (n :: n :: w) ≈₀ w
--     swap : {n : Fin (S m)} {k : Fin (S m)} → (S (k .fst) < (n .fst)) → {w : List (Fin (S m))} → (n :: k :: w) ≈₀ (k :: n :: w)
--     braid : {n : Fin m} {w : List (Fin (S m))} → (S⟨ n ⟩ :: ⟨ n ⟩ :: S⟨ n ⟩ :: w) ≈₀ (⟨ n ⟩ :: S⟨ n ⟩ :: ⟨ n ⟩ :: w)

--     idp : {l : List (Fin (S m))} -> l ≈₀ l
--     comm : {l1 l2 : List (Fin (S m))} -> (l1 ≈₀ l2) -> l2 ≈₀ l1
--     trans : {l1 l2 l3 : List (Fin (S m))} -> (l1 ≈₀ l2) -> (l2 ≈₀ l3) -> l1 ≈₀ l3

--     respects-:: : {l l' : List (Fin (S m))} -> (l ≈₀ l') -> (n : Fin (S m)) -> n :: l ≈₀ n :: l'


data _≈₁_ {m : ℕ} : List (Fin (S m)) → List (Fin (S m)) → Type₀ where
    cancel : {n : Fin (S m)} → (n :: n :: nil) ≈₁ nil
    swap : {n : Fin (S m)} {k : Fin (S m)} → (S (k .fst) < (n .fst)) → (n :: k :: nil) ≈₁ (k :: n :: nil)
    braid : {n : Fin m} → (S⟨ n ⟩ :: ⟨ n ⟩ :: S⟨ n ⟩ :: nil) ≈₁ (⟨ n ⟩ :: S⟨ n ⟩ :: ⟨ n ⟩ :: nil)

    idp : {l : List (Fin (S m))} -> l ≈₁ l
    comm : {l1 l2 : List (Fin (S m))} -> (l1 ≈₁ l2) -> l2 ≈₁ l1
    trans : {l1 l2 l3 : List (Fin (S m))} -> (l1 ≈₁ l2) -> (l2 ≈₁ l3) -> l1 ≈₁ l3

    respects-++ : {l l' r r' : List (Fin (S m))} → (l ≈₁ l') → (r ≈₁ r') → l ++ r ≈₁ l' ++ r'
