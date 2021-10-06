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
