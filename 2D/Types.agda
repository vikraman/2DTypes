module 2D.Types where

open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.Unit

data FT : Set where
  ZERO   : FT
  ONE    : FT
  PLUS   : FT → FT → FT
  TIMES  : FT → FT → FT

⟦_⟧ : FT → Set
⟦ ZERO ⟧         = ⊥
⟦ ONE ⟧          = ⊤
⟦ PLUS t₁ t₂ ⟧   = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧  = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

open import Universe

UFT : Universe _ _
UFT = record { U = FT; El = ⟦_⟧ }

open Universe.Universe UFT public
