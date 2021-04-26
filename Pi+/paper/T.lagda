module T where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function

dist : A × (B ⊎ C) → (A × B) ⊎ (A × C)
dist (a , inj₁ b) = inj₁ (a , b)
dist (a , inj₂ c) = inj₂ (a , c)

factor : (A × B) ⊎ (A × C) → A × (B ⊎ C)
factor inj₁ (a , b) = (a , inj₁ b)
factor inj₂ (a , c) = (a , inj₂ c)

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

unit-elim× : (A × ⊤) → A
unit-elim× (a , tt) = a

unit-elim-2× : (A × ⊤) → A
unit-elim-2× (a , tt) =
    unit-elem+
  ∘ unit-elim-x ⊗ absorb×
  ∘ dist
  ∘ (id ⊗ unit-intro+)
