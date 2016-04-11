module Types' where

open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product

data 𝑈 : Set where
  𝟘 𝟙 : 𝑈
  _⊕_ _⊗_ : 𝑈 → 𝑈 → 𝑈

⟦_⟧ᵤ : 𝑈 → Set
⟦ 𝟘 ⟧ᵤ = ⊥
⟦ 𝟙 ⟧ᵤ = ⊤
⟦ T₁ ⊕ T₂ ⟧ᵤ = ⟦ T₁ ⟧ᵤ ⊎ ⟦ T₂ ⟧ᵤ
⟦ T₁ ⊗ T₂ ⟧ᵤ = ⟦ T₁ ⟧ᵤ × ⟦ T₂ ⟧ᵤ

_⟶_ : 𝑈 → 𝑈 → Set
T₁ ⟶ T₂ = ⟦ T₁ ⟧ᵤ → ⟦ T₂ ⟧ᵤ

-- S / T
data Frac (T : 𝑈) : (S : 𝑈) → Set where
  frac : Frac T 𝟙 -- 1 / T
  _⊞_ : ∀ {S₁ S₂} → Frac T S₁ → Frac T S₂ → Frac T (S₁ ⊕ S₂)
  _⊠_ : ∀ {S₁ S₂} → Frac T S₁ → Frac T S₂ → Frac T (S₁ ⊗ S₂)

module _ {S} where
  ⟦_⟧ : ∀ {T} → Frac S T → Set
  ⟦ frac ⟧ = ⟦ S ⟧ᵤ → (𝟙 ⟶ 𝟙)
  ⟦ T₁ ⊞ T₂ ⟧ = {!!}
  ⟦ T₁ ⊠ T₂ ⟧ = {!!}
