-- {-# OPTIONS --without-K #-}
-- allow K to match on swap₊ in order below ??

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

-- allow K to match on swap₊ ??
order : {τ : U} (p : τ ⟷ τ) → Order p
order (Prim swap₊) = ord 2 (s≤s z≤n) ((id⇔ ⊡ idr◎l) ● rinv◎l)
order {τ} p = orderPostulate {τ} p

