{-# OPTIONS --without-K --exact-split #-}

module Pi+.Coxeter1 where

open import lib.Basics
open import lib.types.Nat
open import lib.types.Fin
open import lib.types.SetQuotient

_↓_ : (n : ℕ) -> (k : ℕ) -> List ℕ
n ↓ 0 = nil
n ↓ (S k) = (k + n) :: (n ↓ k)

postulate
    C : ℕ → Type₀

    module _ (n : ℕ) where
        _↓_ : Fin n -> Fin n -> C n
        _↓_::_ : Fin n -> Fin n → C n → C n

        cancel : ∀ x xs → (x ↓ 1) :: (x ↓ 1) :: xs == xs
        swap : ∀ x y zs → (S x < y) → (y ↓ 1) :: (x ↓ 1) :: zs == (x ↓ 1) :: (y ↓ 1) :: zs
        long : ∀ x y zs → (x ↓ S y) :: (S (x + y) ↓ 1) :: zs == ((x + y) ↓ 1) :: (x ↓ y) :: zs

        trunc : is-set (C n)

-- ∀ xs : C n -> Σ ys (isCanonical ys × (ys == xs))

-- C n <-> C n

This has to be injective Lehmer n -> C n 

Canonical = Σ (C n) isCanonical
Code : (xs ys : Canonical) -> xs == ys -> Prop -- xs ≃ ys
encode : (xs ys : Canonical) -> (p : xs == ys) -> Code p
decode (xs ys : Canonical) -> Code p -> (p : xs == ys)

lemma : (x x' : C n) -> isCanonical x -> isCanonical x' ->
    (x1 ↓ y1) :: (x2 ↓ y2) ::(x3 ↓ y3) ... (xn ↓ yn) == (x1' ↓ y1') :: (x2' ↓ y2') ::(x3' ↓ y3') ... (xn' ↓ yn')
    -> x1 == x1' × y1 == y1' × x2 == x2' ...



(x : Lehmer n) -> c->l (l->c x) == x

data isCanonical : {n : ℕ} → C n -> Set where
    r0 : (x ↓ y) -> 
    isCanonical (x1 ↓ y1) :: (x2 ↓ y2) = x1 > x2
    isCanonical (x1 ↓ y1) :: (x2 ↓ y2) :: rest = isCanonical x1 > x2 && isCanonical ((x2 ↓ y2) :: rest)

-- lemma : ∀ n → C n ≃ Lehmer n