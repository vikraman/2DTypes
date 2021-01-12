{-# OPTIONS --without-K --rewriting #-}

module Pi+.CoxeterParametrized.Coxeter where

open import lib.Base
open import lib.types.Nat using (_+_; <-ap-S; _<_; _≤_)
open import lib.PathGroupoid
open import lib.types.Fin


⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
⟨_⟩ = Fin-S

S⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
S⟨ k , kltn ⟩ = S k , <-ap-S kltn

infixr 35 _∷_

data CList : ℕ → Type₀ where
    [] : ∀ {m} → CList m
    _∷_ : ∀ {m} → Fin (S m) → CList m → CList m

infixr 50 _++_

_++_ : ∀ {m} → CList m → CList m → CList m
_++_ {m} [] l2 = l2
_++_ {m} (x ∷ l1) l2 = x ∷ (l1 ++ l2)

data _≈_ {m : ℕ} : CList m → CList m → Type₀ where
    cancel : {n : Fin (S m)} {w : CList m} → (n ∷ n ∷ w) ≈ w
    swap : {n : Fin (S m)} {k : Fin (S m)} → (S (k .fst) < (n .fst)) → {w : CList m} → (n ∷ k ∷ w) ≈ (k ∷ n ∷ w)
    braid : {n : Fin m} {w : CList m} → (S⟨ n ⟩ ∷ ⟨ n ⟩ ∷ S⟨ n ⟩ ∷ w) ≈ (⟨ n ⟩ ∷ S⟨ n ⟩ ∷ ⟨ n ⟩ ∷ w)

    idp : {l : CList m} -> l ≈ l
    comm : {l1 l2 : CList m} -> (l1 ≈ l2) -> l2 ≈ l1
    trans : {l1 l2 l3 : CList m} -> (l1 ≈ l2) -> (l2 ≈ l3) -> l1 ≈ l3

    respects-∷ : {l l' : CList m} -> (l ≈ l') -> (n : Fin (S m)) -> n ∷ l ≈ n ∷ l'
