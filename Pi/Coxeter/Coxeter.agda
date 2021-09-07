{-# OPTIONS --without-K --rewriting #-}

module Pi.Coxeter.Coxeter where

open import lib.Base
open import lib.types.Nat using (_+_; <-ap-S; _<_; _≤_)
open import lib.NType
open import lib.PathGroupoid
open import lib.types.Fin
open import lib.types.List
open import Pi.Common.Extra

open import Pi.Common.FinHelpers

-- This is the one that is to be used with HIT
-- data _≈₀_ {m : ℕ} : List (Fin (S m)) → List (Fin (S m)) → Type₀ where
--     cancel : {n : Fin (S m)} {w : List (Fin (S m))} → (n :: n :: w) ≈₀ w
--     swap : {n : Fin (S m)} {k : Fin (S m)} → (S (k .fst) < (n .fst)) → {w : List (Fin (S m))} → (n :: k :: w) ≈₀ (k :: n :: w)
--     braid : {n : Fin m} {w : List (Fin (S m))} → (S⟨ n ⟩ :: ⟨ n ⟩ :: S⟨ n ⟩ :: w) ≈₀ (⟨ n ⟩ :: S⟨ n ⟩ :: ⟨ n ⟩ :: w)

--     idp : {l : List (Fin (S m))} -> l ≈₀ l
--     comm : {l1 l2 : List (Fin (S m))} -> (l1 ≈₀ l2) -> l2 ≈₀ l1
--     trans : {l1 l2 l3 : List (Fin (S m))} -> (l1 ≈₀ l2) -> (l2 ≈₀ l3) -> l1 ≈₀ l3

--     respects-:: : {l l' : List (Fin (S m))} -> (l ≈₀ l') -> (n : Fin (S m)) -> n :: l ≈₀ n :: l'

-- data _≈₁_ {m : ℕ} : List (Fin (S m)) → List (Fin (S m)) → Type₀ where
--     cancel : {n : Fin (S m)} → (n :: n :: nil) ≈₁ nil
--     swap : {n : Fin (S m)} {k : Fin (S m)} → (S (k .fst) < (n .fst)) → (n :: k :: nil) ≈₁ (k :: n :: nil)
--     braid : {n : Fin m} → (S⟨ n ⟩ :: ⟨ n ⟩ :: S⟨ n ⟩ :: nil) ≈₁ (⟨ n ⟩ :: S⟨ n ⟩ :: ⟨ n ⟩ :: nil)

--     idp : {l : List (Fin (S m))} -> l ≈₁ l
--     comm : {l1 l2 : List (Fin (S m))} -> (l1 ≈₁ l2) -> l2 ≈₁ l1
--     trans : {l1 l2 l3 : List (Fin (S m))} -> (l1 ≈₁ l2) -> (l2 ≈₁ l3) -> l1 ≈₁ l3

--     respects-++ : {l l' r r' : List (Fin (S m))} → (l ≈₁ l') → (r ≈₁ r') → l ++ r ≈₁ l' ++ r'

data _≈'_ {m : ℕ} : List (Fin (S m)) → List (Fin (S m)) → Type₀ where
    swap : {n : Fin (S m)} {k : Fin (S m)} → (S (k .fst) < (n .fst)) → (n :: k :: nil) ≈' (k :: n :: nil)
    braid : {n : Fin m} → (S⟨ n ⟩ :: ⟨ n ⟩ :: S⟨ n ⟩ :: nil) ≈' (⟨ n ⟩ :: S⟨ n ⟩ :: ⟨ n ⟩ :: nil)
    cancel : {n : Fin (S m)} → (n :: n :: nil) ≈' nil

data _≈*_ : {m : ℕ} → List (Fin m) → List (Fin m) → Type₀ where
    idp : {m : ℕ} {l : List (Fin m)} -> l ≈* l
    comm : {m : ℕ} {l1 l2 : List (Fin m)} -> (l1 ≈* l2) -> l2 ≈* l1
    trans : {m : ℕ} {l1 l2 l3 : List (Fin m)} -> (l1 ≈* l2) -> (l2 ≈* l3) -> l1 ≈* l3
    respects-++ : {m : ℕ} {l l' r r' : List (Fin m)} → (l ≈* l') → (r ≈* r') → l ++ r ≈* l' ++ r'
    ≈-rel : {m : ℕ} {l1 l2 : List (Fin (S m))} → l1 ≈' l2 →  l1 ≈* l2

infixl 20 _■_
_■_ : {m : ℕ} {l1 l2 l3 : List (Fin m)} -> (l1 ≈* l2) -> (l2 ≈* l3) -> l1 ≈* l3
_■_ = trans
