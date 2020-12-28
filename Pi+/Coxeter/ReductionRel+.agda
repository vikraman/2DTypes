{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.ReductionRel+ where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.PathGroupoid

open import Pi+.Misc
open import Pi+.Coxeter.Arithmetic
open import Pi+.Coxeter.Lists
open import Pi+.Coxeter.ReductionRel

data _≅+_ : List -> List -> Type₀ where
    trans≅+ : {m1 m2 m3 : List} -> (m1 ≅ m2) -> (m2 ≅* m3) -> m1 ≅+ m3

ext+ : {l l' : List} -> l ≅ l' -> l ≅+ l'
ext+ p = trans≅+ p idp

ext* : {l l' : List} -> l ≅+ l' -> l ≅* l'
ext* (trans≅+ x x₁) = trans (ext x) x₁

cancel+ : {n : ℕ} -> (l r : List) -> (l ++ n :: n :: r) ≅+ (l ++ r)
cancel+ {n} l r = trans≅+ (cancel≅ l r (l ++ n :: n :: r) (l ++ r) idp idp) idp

swap+ : {n : ℕ} -> {k : ℕ} -> (pk : S k < n) ->  (l r : List) -> (l ++ n :: k :: r) ≅+ (l ++ k :: n :: r)
swap+ {k} {n} pk l r = trans≅+ (swap≅ pk l r (l ++ k :: _ :: r) (l ++ _ :: k :: r) idp idp) idp

long+ : {n : ℕ} -> (k : ℕ) -> (l r : List) -> (l ++ (n ↓ (2 + k)) ++ (1 + k + n) :: r) ≅+ (l ++ (k + n) :: (n ↓ (2 + k)) ++ r)
long+ k l r = ext+ (long≅ k l r _ _ idp idp)

braid+ : {n : ℕ} -> (l r : List) -> (l ++ S n :: n :: S n :: r) ≅+ (l ++ n :: S n :: n :: r)
braid+ {n} l r = long+ {n} 0 l r

trans+ : {m1 m2 m3 : List} -> (m1 ≅+ m2) -> (m2 ≅+ m3) -> m1 ≅+ m3
trans+ (trans≅+ x p) q = trans≅+ x (trans p (ext* q))

trans+* : {m1 m2 m3 : List} -> (m1 ≅+ m2) -> (m2 ≅* m3) -> m1 ≅+ m3
trans+* (trans≅+ x p) q = trans≅+ x (trans p q)

trans*+ : {m1 m2 m3 : List} -> (m1 ≅* m2) -> (m2 ≅+ m3) -> m1 ≅+ m3
trans*+ idp q = q
trans*+ (trans≅ x p) q = trans≅+ x (ext* (trans*+ p q))

+l++ : (l : List) -> {m1 m2 : List} -> (m1 ≅+ m2) -> ((l ++ m1) ≅+ (l ++ m2))
+l++ l (trans≅+ x p) = trans≅+ (l++≅ _ _ l x) ((l++ l p))

++r+ : {m1 m2 : List} -> (r : List) -> (m1 ≅+ m2) -> ((m1 ++ r) ≅+ (m2 ++ r))
++r+ r (trans≅+ x p) = trans≅+ (++r≅ _ _ r x) (++r r p)

-- ≅-abs-l : {x : ℕ} -> (x :: nil) ≅ nil -> ⊥
-- ≅-abs-l (cancel≅ nil r .(_ :: nil) .nil () defmf)
-- ≅-abs-l (cancel≅ (x :: nil) r .(_ :: nil) .nil () defmf)
-- ≅-abs-l (cancel≅ (x :: x₁ :: l) r .(_ :: nil) .nil () defmf)
-- ≅-abs-l (swap≅ x nil r .(_ :: nil) .nil () defmf)
-- ≅-abs-l (swap≅ x (x₁ :: nil) r .(_ :: nil) .nil () defmf)
-- ≅-abs-l (swap≅ x (x₁ :: x₂ :: l) r .(_ :: nil) .nil () defmf)
-- ≅-abs-l (long≅ k nil r .(_ :: nil) .nil defm ())
-- ≅-abs-l (long≅ k (x :: l) r .(_ :: nil) .nil defm ())

-- ≅-abs-r : {x : ℕ} -> nil ≅ (x :: nil) -> ⊥
-- ≅-abs-r (cancel≅ nil r .nil .(_ :: nil) () defmf)
-- ≅-abs-r (cancel≅ (x :: l) r .nil .(_ :: nil) () defmf)
-- ≅-abs-r (swap≅ x nil r .nil .(_ :: nil) () defmf)
-- ≅-abs-r (swap≅ x (x₁ :: l) r .nil .(_ :: nil) () defmf)
-- ≅-abs-r (long≅ k nil r .nil .(_ :: nil) () defmf)
-- ≅-abs-r (long≅ k (x :: l) r .nil .(_ :: nil) () defmf)
-- --
-- empty-reduction : {m : List} -> (nil ≅ m) -> ⊥
-- empty-reduction (cancel≅ nil r .nil _ () defmf)
-- empty-reduction (cancel≅ (x :: l) r .nil _ () defmf)
-- empty-reduction (swap≅ x nil r .nil _ () defmf)
-- empty-reduction (swap≅ x (x₁ :: l) r .nil _ () defmf)
-- empty-reduction (long≅ k nil r .nil mf () defmf)
-- empty-reduction (long≅ k (x :: l) r .nil mf () defmf)

-- one-reduction : {x : ℕ} -> {m : List} -> ([ x ] ≅ m) -> ⊥
-- one-reduction {x} (cancel≅ (x₁ :: nil) r .(x :: nil) mf () defmf)
-- one-reduction {x} (cancel≅ (x₁ :: x₂ :: l) r .(x :: nil) mf () defmf)
-- one-reduction {x} (swap≅ x₁ (x₂ :: nil) r .(x :: nil) mf () defmf)
-- one-reduction {x} (swap≅ x₁ (x₂ :: x₃ :: l) r .(x :: nil) mf () defmf)
-- one-reduction {x} (long≅ k (x₁ :: nil) r .(x :: nil) mf () defmf)
-- one-reduction {x} (long≅ k (x₁ :: x₂ :: l) r .(x :: nil) mf () defmf)