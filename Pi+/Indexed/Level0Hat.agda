{-# OPTIONS --without-K --allow-unsolved-metas --exact-split --rewriting #-}

module Pi+.Indexed.Level0Hat where

open import lib.Base
open import lib.PathGroupoid
open import lib.types.Nat renaming (_+_ to _+ℕ_)
open import lib.types.Sigma
open import lib.types.Fin
open import lib.types.List
open import lib.NType

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.Indexed.Level0
open import Pi+.Indexed.Equiv0Hat
open import Pi+.Indexed.Equiv1Hat
open import Pi+.Indexed.Equiv2Hat

open import Pi+.Misc
open import Pi+.Extra

open import Pi+.Common.FinHelpers
open import Pi+.Coxeter.Coxeter
open import Pi+.Coxeter.Sn

-----------------------------------------------------------------------------
-- Canonical representation of sum types as "lists" I + (I + (I + ... O))

private
  variable
    n m p : ℕ

-----------------------------------------------------------------------------
-- Mapping betweem pi combinators over non-zero types to and from the
-- Coxeter representation

-- Mapping each transposition index to a combinator and
-- some properties

eval^₀⟪_⟫ : (n : ℕ) →  eval^₀ ⟪ n ⟫ == i^ n
eval^₀⟪ O ⟫ = idp
eval^₀⟪ S n ⟫ = ap I+_  eval^₀⟪ n ⟫

postulate
    eval^₀⟪_⟫-rewrite : {n : ℕ} → (eval^₀ ⟪ n ⟫) ↦ i^ n
    {-# REWRITE eval^₀⟪_⟫-rewrite #-}

ℕ-S-is-inj-idp : {n : ℕ} -> ℕ-S-is-inj (S n) (S n) idp == idp
ℕ-S-is-inj-idp = prop-has-all-paths {{has-level-apply ℕ-level _ _}} _ _

-- transpos2pi^ : {n m : ℕ} {t₁ : U^ (S n)} {t₂ : U^ (S m)} → (p : n == m) → Fin n → t₁ ⟷₁^ t₂
-- transpos2pi^ {n = n} {t₁ = t₁} {t₂ = t₂} idp x =
--   let y = eval^₁ (transpos2pi x)
--       z = transport2 _⟷₁^_ (U^-is-Singleton (i^ (S n)) t₁) (U^-is-Singleton (i^ (S n)) t₂) y
--   in  z

transpos2pi^ : {n : ℕ} → Fin n → (i^ (S n)) ⟷₁^ i^ (S n)
transpos2pi^ x = eval^₁ (transpos2pi x)

transpos-cancel^ : {n : ℕ} {k : Fin (S n)} →
                  transpos2pi^ k ◎^ transpos2pi^ k ⟷₂^ id⟷₁^
transpos-cancel^ {n} {k = k} = eval^₂ (transpos-cancel {m = n} {n = k})

slide0-transpos^ : {m : ℕ}  {kp : 0 < S (S (S m))} →
                  (n : Fin (S (S (S m)))) → (1<n : 1 < fst n) →
  transpos2pi^ n ◎^ transpos2pi^ (0 , kp) ⟷₂^ transpos2pi^ (0 , kp) ◎^ transpos2pi^ n
slide0-transpos^ {m} {kp} n 1<n = eval^₂ (slide0-transpos {m} {kp} n 1<n)

slide-transpos^ : {m : ℕ} → (n k : Fin (S m)) → (Sk<n : S (fst k) < fst n) →
  transpos2pi^ n ◎^ transpos2pi^ k ⟷₂^ transpos2pi^ k ◎^ transpos2pi^ n
slide-transpos^ {m} n k Sk<n = eval^₂ (slide-transpos {m} n k Sk<n)

braid-transpos^ : {m : ℕ} → (n : Fin m) →
  transpos2pi^ S⟨ n ⟩ ◎^ transpos2pi^ ⟨ n ⟩ ◎^ transpos2pi^ S⟨ n ⟩ ⟷₂^
  transpos2pi^ ⟨ n ⟩ ◎^ transpos2pi^ S⟨ n ⟩ ◎^ transpos2pi^ ⟨ n ⟩
braid-transpos^ {m} n = eval^₂ (braid-transpos {m} n)

list2norm^ : {m : ℕ} → List (Fin m) → i^ (S m) ⟷₁^ i^ (S m)
list2norm^ l = eval^₁ (list2norm l)

cox≈2pi^ : {m : ℕ} {r₁ r₂ : List (Fin (S m))} → r₁ ≈₁ r₂ → list2norm^ r₁ ⟷₂^ list2norm^ r₂
cox≈2pi^ c = eval^₂ (cox≈2pi c)

piRespectsCox^ : (n : ℕ) → (l₁ l₂ : List (Fin n)) → (l₁ ≈ l₂) →
                (list2norm^ l₁) ⟷₂^ (list2norm^ l₂)
piRespectsCox^ _ _ _ c = eval^₂ (piRespectsCox _ _ _ c)