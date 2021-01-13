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

CoxeterRel  : (n : ℕ) → Rel (List (Fin n)) lzero
CoxeterRel O a b = ⊤
CoxeterRel (S n) = _≈_ {n}

syntax CoxeterRel n x y = x ≈[] y

instance
    CoxeterRel-level : {n : ℕ} → {l1 l2 : List (Fin n)} → is-prop (CoxeterRel n l1 l2)
    CoxeterRel-level = TODO

CoxeterRel-refl : {n : ℕ} → is-refl (CoxeterRel n)
CoxeterRel-refl {O} = λ _ → unit
CoxeterRel-refl {S n} = λ _ → idp

CoxeterRel-sym : {n : ℕ} → is-sym (CoxeterRel n)
CoxeterRel-sym {O} = λ _ → unit
CoxeterRel-sym {S n} = comm

CoxeterRel-trans : {n : ℕ} → is-trans (CoxeterRel n)
CoxeterRel-trans {O} = λ _ _ → unit
CoxeterRel-trans {S n} = trans

Sn : (n : ℕ) → Type lzero
Sn n = SetQuot (CoxeterRel n)

instance
  Sn-level : {n : ℕ} → is-set (Sn n)
  Sn-level = SetQuot-is-set