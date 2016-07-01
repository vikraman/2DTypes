{-# OPTIONS --without-K #-}

module 2D.Order2Lemmas where

open import Data.Bool
open import Data.Nat using (ℕ; suc; _≥_) renaming (_+_ to _ℕ+_)
open import Data.Integer
  using (ℤ; +_; -[1+_])
  renaming (-_ to ℤ-; suc to ℤsuc; _+_ to _ℤ+_)

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary
open import Data.Nat.DivMod using (_mod_)
open import Data.Fin using (Fin; toℕ)
open import Relation.Nullary.Decidable

open import 2D.Types
open import 2D.Iter
open import 2D.Order

------------------------------------------------------------------------------
-- Lemmas useful for foldSwap/unfoldSwap

n≥1⇒n≠0 : ∀ {n} → n ≥ 1 → ¬ (n ≡ 0)
n≥1⇒n≠0 (Data.Nat.s≤s n≥1) ()

mod2 : (n : ℤ) → Fin 2
mod2 (+ n) = n mod 2
mod2 -[1+ n ] = (suc n) mod 2

eqℕ : (n m : ℕ) → Bool
eqℕ ℕ.zero ℕ.zero = true
eqℕ ℕ.zero (suc m) = false
eqℕ (suc n) ℕ.zero = false
eqℕ (suc n) (suc m) = eqℕ n m

negModn : (n m : ℕ) → ℕ
negModn ℕ.zero m = ℕ.zero
negModn (suc n) m = (toℕ (m mod (suc n))) ℕ+ (suc n)

mmod : (m n : ℕ) → n ≥ 1 → ℕ
mmod m n n≥1 = toℕ (_mod_ m n {fromWitnessFalse (n≥1⇒n≠0 n≥1)})

{-
_⇔?_ : {τ : U} {p : τ ⟷ τ} → (q r : Iter p) → Bool
_⇔?_ {p = p} (perm i q α) (perm j r γ) with order p
perm (+_ n₁) q α ⇔? perm (+_ n₂) r γ | ord n n≥1 p^n⇔id⟷ =
  eqℕ (mmod n₁ n n≥1) (mmod n₂ n n≥1)
perm (+_ n₁) q α ⇔? perm (-[1+_] n₂) r γ | ord n n≥1 p^n⇔id⟷ =
  eqℕ (mmod n₁ n n≥1) (mmod (negModn n n₂) n n≥1)
perm (-[1+_] n₁) q α ⇔? perm (+_ n₂) r γ | ord n n≥1 p^n⇔id⟷ =
  eqℕ (mmod (negModn n n₁) n n≥1) (mmod n₂ n n≥1)
perm (-[1+_] n₁) q α ⇔? perm (-[1+_] n₂) r γ | ord n n≥1 p^n⇔id⟷ =
  eqℕ (mmod n₁ n n≥1) (mmod n₂ n n≥1)
-}

--------------------------------------------------


