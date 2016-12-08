{-# OPTIONS --without-K #-}

module 2D.Order where

open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Integer as ℤ

open import 2D.Types
open import 2D.Power

record Order {τ : U} (p : τ ⟷ τ) : Set where
  constructor ord
  field
    n : ℕ -- the least such n
    n≥1 : n ≥ 1
    p^n⇔id⟷ : p ^ (+ n) ⇔ Prim id⟷

postulate
  orderPostulate : {τ : U} (p : τ ⟷ τ) → Order p

-- latest version of paper has a lemma relating to order, proven here
lemma4 : {τ : U} (p : τ ⟷ τ) (n : ℤ) →
  let k = Order.n (orderPostulate p) in p ^ (ℤ.+ k ℤ.+ n) ⇔ p ^ n
lemma4 p n = lower {p = p} (ℤ.+ (Order.n (orderPostulate p))) n ● Order.p^n⇔id⟷ (orderPostulate p) ⊡ id⇔ ● idl◎l
