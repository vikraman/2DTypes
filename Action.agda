module _ where

open import Agda.Primitive
open import Algebra
open import Algebra.Structures
open import Categories.Category
open import Categories.Groupoid
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Function

record Action {c ℓ s} (G′ : Group c ℓ) (S : Set s) : Set (s ⊔ c) where
  open Group G′ renaming (Carrier to G) hiding (trans; isEquivalence)
  field
    ρ : G × S → S
    identityA : ∀ {x} → ρ (ε , x) ≡ x
    compatibility : ∀ {g h x} → ρ (g ∙ h , x) ≡ ρ (g , ρ (h , x))

  C : Category _ _ _
  C = record { Obj = S
             ; _⇒_ = λ s s′ → Σ[ g ∈ G ] ρ (g , s) ≡ s′
             ; _≡_ = _≡_ -- setoid?
             ; id = ε , identityA
             -- ≡-Reasoning?
             ; _∘_ = λ { (g′ , s′) (g , s) → g′ ∙ g , trans compatibility (trans (cong (λ s → ρ (g′ , s)) s) s′) }
             ; assoc = {!!}
             ; identityˡ = {!!}
             ; identityʳ = {!!}
             ; equiv = isEquivalence
             ; ∘-resp-≡ = {!!}
             }

  inv : ∀ g → g ∙ g ⁻¹ ≈ ε
  inv = proj₂ inverse

  isGroupoid : Groupoid C
  isGroupoid = record { _⁻¹ = λ { (g , s) → {!!} , {!!} }
                      ; iso = {!!}
                      }
