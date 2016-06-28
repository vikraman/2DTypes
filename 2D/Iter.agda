module 2D.Iter where

open import 2D.Types
open import 2D.Power

open import Data.Integer as ℤ hiding (∣_∣)

record Iter {τ : U} (p : τ ⟷ τ) : Set where
  constructor <_,_,_>
  field
    k : ℤ
    q : τ ⟷ τ
    α : q ⇔ p ^ k
