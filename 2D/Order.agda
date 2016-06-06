module 2D.Order where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import 2D.Types

pⁿ : {τ : U} → (τ ⟷ τ) → ℕ → (τ ⟷ τ)
pⁿ p zero = id⟷
pⁿ p (suc n) = p ◎ pⁿ p n

record Order {τ : U} (p : τ ⟷ τ) : Set where
  constructor ord
  field
    n : ℕ -- the least such n
    n≥1 : n ≥ 1
    -- apⁿ : ∀ v → ap (pⁿ p n) v ≡ v
    -- !apⁿ : ∀ v → ap (pⁿ (! p) n) v ≡ v

postulate
  order : {τ : U} (p : τ ⟷ τ) → Order p
