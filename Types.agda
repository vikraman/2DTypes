module _ where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Universe

data U : Set where
  𝟘 : U
  𝟙 : U
  _⊕_ : U → U → U
  _⊗_ : U → U → U

⟦_⟧ : U → Set
⟦ 𝟘 ⟧ = ⊥
⟦ 𝟙 ⟧ = ⊤
⟦ t₁ ⊕ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ t₁ ⊗ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

U-univ : Universe _ _
U-univ = record { U = U ; El = ⟦_⟧ }

open import Data.Nat

∣_∣ : U → ℕ
∣ 𝟘 ∣ = 0
∣ 𝟙 ∣ = 1
∣ t₁ ⊕ t₂ ∣ = ∣ t₁ ∣ + ∣ t₂ ∣
∣ t₁ ⊗ t₂ ∣ = ∣ t₁ ∣ * ∣ t₂ ∣

open import Function
open import Categories.Category
open import Relation.Binary.PropositionalEquality

∘-resp-≡ : {A B C : Set} {f h : B → C} {g i : A → B} → f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i
∘-resp-≡ refl refl = refl

U-cat : Category _ _ _
U-cat = record { Obj = U
               ; _⇒_ = λ a b → ⟦ a ⟧ → ⟦ b ⟧
               ; _≡_ = _≡_
               ; id = id
               ; _∘_ = λ g f → g ∘ f
               ; assoc = refl
               ; identityˡ = refl
               ; identityʳ = refl
               ; equiv = isEquivalence
               ; ∘-resp-≡ = ∘-resp-≡
               }
