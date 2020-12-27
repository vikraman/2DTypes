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

infixr 60 _:⟨_⟩:_

data _>>_ (n : ℕ) : List -> Type₀ where
  nil : n >> nil
  _:⟨_⟩:_ : {l : List} -> (k : ℕ) -> (k < n) -> n >> l -> n >> (k :: l)

ListN : (n : ℕ) → Type₀
ListN n = Σ List λ xs -> n >> xs

data LL (n : ℕ) : Type₀ where
  nil : LL n
  _:[_]:_ : (k : ℕ) (p : k < n) (xs : LL n) → LL n

instance
    ListN-level : {n : ℕ} → is-set (ListN n)
    ListN-level = TODO

syntax CoxeterRel n x y = x ≈[ n ] y

data CoxeterRel (n : ℕ) : Rel (LL n) lzero where
  cancel≈ : {k : ℕ} -> (p : k < n) -> (k :[ p ]: (k :[ p ]: nil)) ≈[ n ] nil
  -- swap≈ : {o : ℕ} -> (q : o < n) -> {k : ℕ} -> (p : k < n) -> (S k < o) -> (o :[ q ]: k :[ p ]: nil) ≈[ n ] (k :[ p ]: o :[ q ]: nil)
  -- braid≈ : {o : ℕ} -> (p : o < n) -> (q : (S o) < n) -> ((S o) :[ q ]: o :[ p ]: (S o) :[ q ]: nil) ≈[ n ] (o :[ p ]: (S o) :[ q ]: o :[ p ]: nil)
  respects-l≈ : (l : ListN) -> {r r' lr lr' : ListN} -> (r ≈[ n ] r') -> (lr == l ++ r) -> (lr' == l ++ r') -> lr ≈[ n ] lr'
  respects-r≈ : {l l' : ListN} -> (r : ListN) ->{lr l'r : ListN} -> (l ≈[ n ] l') -> (lr == l ++ r) -> (l'r == l' ++ r) -> lr ≈[ n ] l'r
  idp≈ : {m : ListN} -> m ≈[ n ] m
  comm≈ : {m1 m2 : ListN} -> (m1 ≈[ n ] m2) -> m2 ≈[ n ] m1
  trans≈ : {m1 m2 m3 : ListN} -> (m1 ≈[ n ] m2) -> (m2 ≈[ n ] m3) -> m1 ≈[ n ] m3

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