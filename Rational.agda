module Rational where

open import Data.Nat

record ℚ : Set where
  constructor _/_
  field
    p q : ℕ

postulate
  _++_ : ℚ → ℚ → ℚ
