{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Coxeter where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.PathGroupoid

open import Pi+.Misc
open import Pi+.Coxeter.Arithmetic
open import Pi+.Coxeter.Lists
open import Pi+.Coxeter.MCoxeter
open import Pi+.Coxeter.Diamond

open ≅*-Reasoning

variable
    n : ℕ

data _≃_ : List -> List -> Set where
  comm≅ : {m1 m2 mf : List} -> (p1 : m1 ≅* mf) -> (p2 : m2 ≅* mf) -> m1 ≃ m2

refl≃ : (m : List) -> (m ≃ m)
refl≃ m = comm≅ idp idp

comm≃ : (m1 m2 : List) -> (m1 ≃ m2) -> (m2 ≃ m1)
comm≃ m1 m2 (comm≅ p1 p2) = comm≅ p2 p1

trans≃ : (m1 m2 m3 : List) -> (r1 : m1 ≃ m2) -> (r2 : m2 ≃ m3) -> (m1 ≃ m3)
trans≃ m1 m2 m3 (comm≅ p1 p2) (comm≅ p3 p4) =
  let lemma-m , lemma1 , lemma2 = diamond-full p2 p3
  in  comm≅ (trans p1 lemma1) (trans p4 lemma2)

-- True coxeter presentation
data _~_ : List -> List -> Set where
  cancel~ : (n :: n :: nil) ~ nil
  swap~ : {k : ℕ} -> (S k < n) -> (n :: k :: nil) ~ (k :: n :: nil)
  braid~ : ((S n) :: n :: (S n) :: nil) ~ (n :: (S n) :: n :: nil)
  respects-r~ : (l : List) -> {r r' lr lr' : List} -> (r ~ r') -> (lr == l ++ r) -> (lr' == l ++ r') -> lr ~ lr'
  respects-l~ : {l l' : List} -> (r : List) ->{lr l'r : List} -> (l ~ l') -> (lr == l ++ r) -> (l'r == l' ++ r) -> lr ~ l'r
  idp~ : {m : List} -> m ~ m
  comm~ : {m1 m2 : List} -> (m1 ~ m2) -> m2 ~ m1
  trans~ : {m1 m2 m3 : List} -> (m1 ~ m2) -> (m2 ~ m3) -> m1 ~ m3

long-swap-lemma : (n k x : ℕ) -> (k + n < x) -> ((n ↓ k) ++ x :: nil) ~ (x :: (n ↓ k))
long-swap-lemma n 0 x p = idp~
long-swap-lemma n (S k) x p = trans~ (respects-r~ [ k + n ] (long-swap-lemma n k x (≤-down p)) idp idp) (respects-l~ (n ↓ k) (comm~ (swap~ p)) idp idp)

long-lemma : (n k : ℕ) -> ((n ↓ (2 + k)) ++ S (k + n) :: nil) ~ (k + n :: (n ↓ (2 + k)))
long-lemma n 0 = braid~
long-lemma n (S k) = trans~ (respects-r~ (_ :: _ :: nil) (long-swap-lemma n (1 + k) (2 + k + n) rrr) idp idp) (respects-l~ _ braid~ idp idp)

mcoxeter≅->coxeter : (m1 m2 : List) -> (m1 ≅ m2) -> (m1 ~ m2)
mcoxeter≅->coxeter m1 m2 (cancel≅ l r .m1 .m2 defm defmf) = respects-r~ l (respects-l~ r cancel~ idp idp) defm defmf
mcoxeter≅->coxeter m1 m2 (swap≅ x l r .m1 .m2 defm defmf) = respects-r~ l (respects-l~ r (swap~ x) idp idp) defm defmf
mcoxeter≅->coxeter m1 m2 (long≅ {n} k nil r .m1 .m2 defm defmf) = respects-l~ r (long-lemma n k) (≡-trans defm (≡-sym (++-assoc (n ↓ (2 + k)) [ 1 + k + n ] r))) defmf
mcoxeter≅->coxeter (x₁ :: m1) (x₂ :: m2) (long≅ k (x :: l) r .(x₁ :: m1) .(x₂ :: m2) defm defmf) =
  let rec = mcoxeter≅->coxeter m1 m2 (long≅ k l r m1 m2 (cut-head defm) (cut-head defmf))
  in  respects-r~ [ x ] rec (head+tail (cut-tail defm) idp) (head+tail (cut-tail defmf) idp)

mcoxeter≅*->coxeter : (m1 m2 : List) -> (m1 ≅* m2) -> (m1 ~ m2)
mcoxeter≅*->coxeter m1 .m1 idp = idp~
mcoxeter≅*->coxeter m1 m2 (trans≅ x p) = trans~ ((mcoxeter≅->coxeter _ _ x)) ((mcoxeter≅*->coxeter _ _ p))

mcoxeter->coxeter : (m1 m2 : List) -> (m1 ≃ m2) -> (m1 ~ m2)
mcoxeter->coxeter m1 m2 (comm≅ p1 p2) = trans~ (mcoxeter≅*->coxeter _ _ p1) (comm~ ((mcoxeter≅*->coxeter _ _ p2)))
