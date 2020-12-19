{-# OPTIONS --without-K --exact-split #-}

module Pi+.Coxeter where

open import lib.Basics
open import lib.types.Nat
open import lib.types.Fin
open import lib.types.List
open import lib.types.SetQuotient

_↓_ : (n : ℕ) -> (k : ℕ) -> List ℕ
n ↓ 0 = nil
n ↓ (S k) = (k + n) :: (n ↓ k)

-- R1
data _→_ : Rel (List ℕ) lzero where
    cancel→ : {a : ℕ} -> (l r m mf : List ℕ) -> (defm : m == l ++ (a :: a :: r)) -> (defmf : mf == l ++ r) -> (m → mf)
    swap→ : {a k : ℕ} -> (S k < a ) ->  (l r m mf : List ℕ) -> (defm : m == l ++ (a :: k :: r)) -> (defmf : mf == l ++ (k :: a :: r)) -> (m → mf)
    long→ : (a k : ℕ) -> (l r m mf : List ℕ) -> (defm : m == l ++ (a ↓ (2 + k)) ++ ((1 + k + a) :: r)) -> (defmf : mf == l ++ ((k + a) :: (a ↓ (2 + k))) ++ r) -> (m → mf)

-- R2
data _→*_ : Rel (List ℕ) lzero where
    refl→ : {m : List ℕ} -> m →* m
    trans→ : {m1 m2 m3 : List ℕ} -> (m1 → m2) -> (m2 →* m3) -> m1 →* m3

-- R3
_≃_ : Rel (List ℕ) lzero
xs ≃ ys = Σ mf (xs →* mf × ys →* mf)

-- l1 = NOT ∘ NOT ∘ NOT

-- l1 ≃ l1 = 
--  fst = mf = NOT
 
--  snd: (l1 →* mf) × (l1 →* mf)
--  snd = (reduces first two NOTs), (reduces last two NOTs)


_≈_ : {n : ℕ} → Rel (List (Fin n)) _
xs ≈ ys = map fst xs ≃ map fst ys

≈-is-prop : {n : ℕ} {xs ys : List (Fin n)} → is-prop (xs ≈ ys)
≈-is-prop {n} {xs} {ys} = has-level-in λ p q → {!   !}

≈-is-prop-aux : {n : ℕ} {xs ys : List (Fin n)} → (p q : xs ≈ ys) → p == q
≈-is-prop-aux {n} {xs} {ys} p q = {! p !}

{- 
≈-is-refl : {n : ℕ} {xs : List (Fin n)} → xs ≈ xs
≈-is-sym : {n : ℕ} {xs ys : List (Fin n)} → xs ≈ ys → ys ≈ xs
≈-is-trans : {n : ℕ} {xs ys zs : List (Fin n)} → is-trans (xs ≈ ys)
 -}
-- ∀ n → LehmerCode n ≃ List (Fin n) / ≈--  snd = (reduces first two NOTs), (reduces last two NOTs)


_≈_ : {n : ℕ} → Rel (List (Fin n)) _
xs ≈ ys = map fst xs ≃ map fst ys

≈-is-prop : {n : ℕ} {xs ys : List (Fin n)} → is-prop (xs ≈ ys)
≈-is-prop {n} {xs} {ys} = has-level-in λ p q → {!   !}

≈-is-prop-aux : {n : ℕ} {xs ys : List (Fin n)} → (p q : xs ≈ ys) → p == q
≈-is-prop-aux {n} {xs} {ys} p q = {! p !}

{- 
≈-is-refl : {n : ℕ} {xs : List (Fin n)} → xs ≈ xs
≈-is-sym : {n : ℕ} {xs ys : List (Fin n)} → xs ≈ ys → ys ≈ xs
≈-is-trans : {n : ℕ} {xs ys zs : List (Fin n)} → is-trans (xs ≈ ys)
 -}
-- ∀ n → LehmerCode n ≃ List (Fin n) / ≈