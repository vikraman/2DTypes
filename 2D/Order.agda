module 2D.Order where

open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Integer as ℤ
open import 2D.Types

infix 40 _^_

_^_ : {τ : U} → (p : τ ⟷ τ) → (k : ℤ) → (τ ⟷ τ)
p ^ (+ 0) = Prim id⟷
p ^ (+ (suc k)) = p ◎ (p ^ (+ k))
p ^ -[1+ 0 ] = ! p
p ^ (-[1+ (suc k) ]) = (! p) ◎ (p ^ -[1+ k ])


record Order {τ : U} (p : τ ⟷ τ) : Set where
  constructor ord
  field
    n : ℕ -- the least such n
    n≥1 : n ≥ 1
    p^n⇔id⟷ : p ^ (+ n) ⇔ Prim id⟷

postulate
  order : {τ : U} (p : τ ⟷ τ) → Order p
