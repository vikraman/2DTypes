{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Parametrized.Group where

open import lib.Base
open import lib.Relation
open import lib.NType
open import lib.types.SetQuotient public
open import lib.types.List
open import lib.types.Fin

open import Pi+.Extra
open import Pi+.Coxeter.Parametrized.Coxeter

CoxeterRel  : (n : ℕ) → Rel (List (Fin (S n))) lzero
CoxeterRel n = _≈₁_ {n}

-- instance
--     CoxeterRel-level : {n : ℕ} → {l1 l2 : List (Fin (S n))} → is-prop (CoxeterRel n l1 l2)
--     CoxeterRel-level = TODO

CoxeterRel-refl : {n : ℕ} → is-refl (CoxeterRel n)
CoxeterRel-refl {n} = λ _ → idp

CoxeterRel-sym : {n : ℕ} → is-sym (CoxeterRel n)
CoxeterRel-sym {n} = comm

CoxeterRel-trans : {n : ℕ} → is-trans (CoxeterRel n)
CoxeterRel-trans {n} = trans

Sn : (n : ℕ) → Type lzero
Sn n = SetQuot (CoxeterRel n)

instance
  Sn-level : {n : ℕ} → is-set (Sn n)
  Sn-level = SetQuot-is-set