\begin{code}
module T where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function

variable
  A B C D : Set

dist : A × (B ⊎ C) → (A × B) ⊎ (A × C)
dist (a , inj₁ b) = inj₁ (a , b)
dist (a , inj₂ c) = inj₂ (a , c)

factor : (A × B) ⊎ (A × C) → A × (B ⊎ C)
factor (inj₁ (a , b)) = (a , inj₁ b)
factor (inj₂ (a , c)) = (a , inj₂ c)

unit-intro+ : A → (A ⊎ ⊥)
unit-intro+ a = inj₁ a

unit-elim+ : (A ⊎ ⊥) → A
unit-elim+ (inj₁ a) = a
unit-elim+ (inj₂ ())

unit-intro× : A → (A × ⊤)
unit-intro× a = (a , tt)

unit-elim× : (A × ⊤) → A
unit-elim× (a , tt) = a

absorb× : A × ⊥ → ⊥
absorb× ()

_⊗_ : (A → B) → (C → D) → A × C → B × D
(f ⊗ g) (a , b) = f a , g b

-- unit-elim-2× : (A × ⊤) → A
-- unit-elim-2× (a , tt) =
--     unit-elim+
--   ∘ unit-elim× ⊗ absorb×
--   ∘ dist
--   ∘ (id ⊗ unit-intro+)
\end{code}
