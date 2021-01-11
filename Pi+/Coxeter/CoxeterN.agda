{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.CoxeterN where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.PathOver
open import lib.types.Nat using (_+_; <-ap-S; _<_; _≤_)
open import lib.types.Sigma
open import lib.PathGroupoid
open import lib.Funext
open import lib.types.Pi
open import lib.types.Fin

-- open import Pi+.Misc
-- open import Pi+.Coxeter.Arithmetic
-- open import Pi+.Coxeter.Lists
-- open import Pi+.Coxeter.ReductionRel
-- open import Pi+.Coxeter.MCoxeter
-- open import Pi+.Coxeter.MCoxeterS
-- open import Pi+.Coxeter.Diamond


module Zero where
    ⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
    ⟨_⟩ = Fin-S

    S⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
    S⟨ k , kltn ⟩ = S k , <-ap-S kltn

    infixr 35 _::_

    data CList : ℕ → Type₀ where
        nil : ∀ {m} → CList m
        _::_ : ∀ {m} → Fin (S m) → CList m → CList m

    infixr 50 _++_

    _++_ : ∀ {m} → CList m → CList m → CList m
    _++_ {m} nil l2 = l2
    _++_ {m} (x :: l1) l2 = x :: (l1 ++ l2)

    data _≈₀_ {m : ℕ} : CList m → CList m → Type₀ where
        cancel : {n : Fin (S m)} {w : CList m} → (n :: n :: w) ≈₀ w
        swap : {n : Fin (S m)} {k : Fin (S m)} → (S (k .fst) < (n .fst)) → {w : CList m} → (n :: k :: w) ≈₀ (k :: n :: w)
        braid : {n : Fin m} {w : CList m} → (S⟨ n ⟩ :: ⟨ n ⟩ :: S⟨ n ⟩ :: w) ≈₀ (⟨ n ⟩ :: S⟨ n ⟩ :: ⟨ n ⟩ :: w)

        idp : {l : CList m} -> l ≈₀ l
        comm : {l1 l2 : CList m} -> (l1 ≈₀ l2) -> l2 ≈₀ l1
        trans : {l1 l2 l3 : CList m} -> (l1 ≈₀ l2) -> (l2 ≈₀ l3) -> l1 ≈₀ l3

        respects-++ : {l l' r r' : CList m} -> (l ≈₀ l') -> (r ≈₀ r') -> l ++ r ≈₀ l' ++ r


module One where 
    open import lib.types.List

    ⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
    ⟨_⟩ = Fin-S

    S⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
    S⟨ k , kltn ⟩ = S k , <-ap-S kltn

    data _≈₁_ {m : ℕ} : List (Fin (S m)) → List (Fin (S m)) → Type₀ where
        cancel : {n : Fin (S m)} → (n :: n :: nil) ≈₁ nil
        swap : {n : Fin (S m)} {k : Fin (S m)} → (S (k .fst) < (n .fst)) → (n :: k :: nil) ≈₁ (k :: n :: nil)
        braid : {n : Fin m} → (S⟨ n ⟩ :: ⟨ n ⟩ :: S⟨ n ⟩ :: nil) ≈₁ (⟨ n ⟩ :: S⟨ n ⟩ :: ⟨ n ⟩ :: nil)

        idp : {m : List (Fin (S m))} -> m ≈₁ m
        comm : {m1 m2 : List (Fin (S m))} -> (m1 ≈₁ m2) -> m2 ≈₁ m1
        trans : {m1 m2 m3 : List (Fin (S m))} -> (m1 ≈₁ m2) -> (m2 ≈₁ m3) -> m1 ≈₁ m3

        respects-++ : {l l' r r' : List (Fin (S m))} -> (l ≈₁ l') -> (r ≈₁ r') -> l ++ r ≈₁ l' ++ r


module Two where
    open import lib.types.List

    _>>_ : ℕ -> List ℕ -> Type₀
    n >> l = All (λ x → x < n) l

    data _≈₂[_]_ : List ℕ → ℕ → List ℕ → Type₀ where
        cancel : {n : ℕ} → (n :: n :: nil) ≈₂[ n ] nil
        swap : {n : ℕ} {k : ℕ} → (k < n) → (n :: k :: nil) ≈₂[ n ] (k :: n :: nil)
        braid : {n : ℕ} → (S n :: n :: S n :: nil) ≈₂[ S n ] ( n :: S n :: n :: nil)

        idp : {n : ℕ} → {l : List ℕ} -> (S n >> l) -> l ≈₂[ n ] l
        comm : {n : ℕ} → {l1 l2 : List ℕ} -> (l1 ≈₂[ n ] l2) -> l2 ≈₂[ n ] l1
        trans : {n : ℕ} → {l1 l2 l3 : List ℕ} -> (l1 ≈₂[ n ] l2) -> (l2 ≈₂[ n ] l3) -> l1 ≈₂[ n ] l3

        respects-++ : {n : ℕ} {l l' r r' : List ℕ} -> (l ≈₂[ n ] l') -> (r ≈₂[ n ] r') -> l ++ r ≈₂[ n ] l' ++ r

        lift : {n k : ℕ} -> (n ≤ k) -> (l r : List ℕ) -> l ≈₂[ n ] r -> l ≈₂[ k ] r