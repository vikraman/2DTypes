{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Parametrized.Group where

open import lib.Base
open import lib.Relation
open import lib.NType
open import lib.types.SetQuotient public

open import Pi+.Extra
open import Pi+.Coxeter.Parametrized.Coxeter

CoxeterRel  : (n : ℕ) → Rel (CList n) lzero
CoxeterRel n = _≈_ {n}

syntax CoxeterRel n x y = x ≈[ n ] y

instance
    CoxeterRel-level : {n : ℕ} → {l1 l2 : CList n} → is-prop (CoxeterRel n l1 l2)
    CoxeterRel-level = TODO

CoxeterRel-refl : {n : ℕ} → is-refl (CoxeterRel n)
CoxeterRel-refl = λ a → idp

CoxeterRel-sym : {n : ℕ} → is-sym (CoxeterRel n)
CoxeterRel-sym = comm

CoxeterRel-trans : {n : ℕ} → is-trans (CoxeterRel n)
CoxeterRel-trans = trans

Sn : (n : ℕ) → Type lzero
Sn n = SetQuot (CoxeterRel n)

instance
  Sn-level : {n : ℕ} → is-set (Sn n)
  Sn-level = SetQuot-is-set