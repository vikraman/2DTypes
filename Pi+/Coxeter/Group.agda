{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Group where

open import lib.Base
open import lib.Relation
open import lib.NType
open import lib.types.SetQuotient public

open import Pi+.Coxeter.Arithmetic
open import Pi+.Coxeter.Lists
open import Pi+.Coxeter.Coxeter
open import Pi+.Extra

data _>>_ (n : ℕ) : List -> Type₀ where
  nil : n >> nil
  _:⟨_⟩:_ : {l : List} -> (k : ℕ) -> (k < n) -> n >> l -> n >> (k :: l)

ListN : (n : ℕ) → Type₀
ListN n = Σ List λ xs -> n >> xs

instance
    ListN-level : {n : ℕ} → is-set (ListN n)
    ListN-level = TODO

CoxeterRel  : (n : ℕ) → Rel (ListN n) lzero
CoxeterRel = TODO

syntax CoxeterRel n x y = x ≈[ n ] y

instance
    CoxeterRel-level : {n : ℕ} → {l1 l2 : ListN n} → is-prop (CoxeterRel n l1 l2)
    CoxeterRel-level = TODO

CoxeterRel-refl : {n : ℕ} → is-refl (CoxeterRel n)
CoxeterRel-refl = TODO

CoxeterRel-sym : {n : ℕ} → is-sym (CoxeterRel n)
CoxeterRel-sym = TODO

CoxeterRel-trans : {n : ℕ} → is-trans (CoxeterRel n)
CoxeterRel-trans = TODO

Sn : (n : ℕ) → Type lzero
Sn n = SetQuot (CoxeterRel n)

instance
  Sn-level : {n : ℕ} → is-set (Sn n)
  Sn-level = SetQuot-is-set