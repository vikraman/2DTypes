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

-- conveniently lift a combinator to its 1-iterate
iter : {τ : U} → (p : τ ⟷ τ) → Iter p
iter p = < + 1 , p , idr◎r >

-- zeroth iteration of any combinator
zeroth : {τ : U} → (p : τ ⟷ τ) → Iter p
zeroth p = < + 0 , Prim id⟷ , id⇔ >
