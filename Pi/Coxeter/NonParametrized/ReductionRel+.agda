{-# OPTIONS --without-K --rewriting #-}

module Pi.Coxeter.NonParametrized.ReductionRel+ where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.PathGroupoid

open import Pi.Common.Misc
open import Pi.Common.Arithmetic
open import Pi.Common.ListN
open import Pi.Coxeter.NonParametrized.ReductionRel

data _≅+_ : Listℕ -> Listℕ -> Type₀ where
    trans≅+ : {m1 m2 m3 : Listℕ} -> (m1 ≅ m2) -> (m2 ≅* m3) -> m1 ≅+ m3

ext+ : {l l' : Listℕ} -> l ≅ l' -> l ≅+ l'
ext+ p = trans≅+ p idp

ext* : {l l' : Listℕ} -> l ≅+ l' -> l ≅* l'
ext* (trans≅+ x x₁) = trans (ext x) x₁

cancel+ : {n : ℕ} -> (l r : Listℕ) -> (l ++ n ∷ n ∷ r) ≅+ (l ++ r)
cancel+ {n} l r = trans≅+ (cancel≅ l r (l ++ n ∷ n ∷ r) (l ++ r) idp idp) idp

swap+ : {n : ℕ} -> {k : ℕ} -> (pk : S k < n) ->  (l r : Listℕ) -> (l ++ n ∷ k ∷ r) ≅+ (l ++ k ∷ n ∷ r)
swap+ {k} {n} pk l r = trans≅+ (swap≅ pk l r (l ++ k ∷ _ ∷ r) (l ++ _ ∷ k ∷ r) idp idp) idp

long+ : {n : ℕ} -> (k : ℕ) -> (l r : Listℕ) -> (l ++ (n ↓ (2 + k)) ++ (1 + k + n) ∷ r) ≅+ (l ++ (k + n) ∷ (n ↓ (2 + k)) ++ r)
long+ k l r = ext+ (long≅ k l r _ _ idp idp)

braid+ : {n : ℕ} -> (l r : Listℕ) -> (l ++ S n ∷ n ∷ S n ∷ r) ≅+ (l ++ n ∷ S n ∷ n ∷ r)
braid+ {n} l r = long+ {n} 0 l r

trans+ : {m1 m2 m3 : Listℕ} -> (m1 ≅+ m2) -> (m2 ≅+ m3) -> m1 ≅+ m3
trans+ (trans≅+ x p) q = trans≅+ x (trans p (ext* q))

trans+* : {m1 m2 m3 : Listℕ} -> (m1 ≅+ m2) -> (m2 ≅* m3) -> m1 ≅+ m3
trans+* (trans≅+ x p) q = trans≅+ x (trans p q)

trans*+ : {m1 m2 m3 : Listℕ} -> (m1 ≅* m2) -> (m2 ≅+ m3) -> m1 ≅+ m3
trans*+ idp q = q
trans*+ (trans≅ x p) q = trans≅+ x (ext* (trans*+ p q))

+l++ : (l : Listℕ) -> {m1 m2 : Listℕ} -> (m1 ≅+ m2) -> ((l ++ m1) ≅+ (l ++ m2))
+l++ l (trans≅+ x p) = trans≅+ (l++≅ _ _ l x) ((l++ l p))

++r+ : {m1 m2 : Listℕ} -> (r : Listℕ) -> (m1 ≅+ m2) -> ((m1 ++ r) ≅+ (m2 ++ r))
++r+ r (trans≅+ x p) = trans≅+ (++r≅ _ _ r x) (++r r p)
