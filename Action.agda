module _ where

open import Agda.Primitive
open import Algebra
open import Categories.Category
open import Categories.Groupoid
open import Data.Product
open import Relation.Binary.PropositionalEquality

record Action {c ℓ s} (G′ : Group c ℓ) (S : Set s) : Set (s ⊔ c ⊔ ℓ) where
  open Group G′ renaming (Carrier to G) hiding (isEquivalence ; sym)
  field
    ρ : G × S → S
    ρ-resp-≈ : ∀ {g g′ s} → g ≈ g′ → ρ (g , s) ≡ ρ (g′ , s)
    identityA : ∀ {x} → ρ (ε , x) ≡ x
    compatibility : ∀ {g h x} → ρ (g ∙ h , x) ≡ ρ (g , ρ (h , x))

  C : Category _ _ _
  C = record { Obj = S
             ; _⇒_ = λ s s′ → Σ[ g ∈ G ] ρ (g , s) ≡ s′
             ; _≡_ = _≡_
             ; id = ε , identityA
             ; _∘_ = _∘_
             ; assoc = {!!}
             ; identityˡ = {!!}
             ; identityʳ = {!!}
             ; equiv = isEquivalence
             ; ∘-resp-≡ = {!!}
             }
    where _∘_ : ∀ {A B C}
              → Σ[ g ∈ G ] ρ (g , B) ≡ C → Σ[ g ∈ G ] ρ (g , A) ≡ B
              → Σ[ g ∈ G ] ρ (g , A) ≡ C
          _∘_ {A} {B} {C} (g′ , ρB≡C) (g , ρA≡B) = g′ ∙ g , let open ≡-Reasoning in
            begin
              ρ (g′ ∙ g , A)
            ≡⟨ compatibility ⟩
              ρ (g′ , ρ (g , A))
            ≡⟨ cong (λ s → ρ (g′ , s)) ρA≡B ⟩
              ρ (g′ , B)
            ≡⟨ ρB≡C ⟩
              C
            ∎

  isGroupoid : Groupoid C
  isGroupoid = record { _⁻¹ = inv
                      ; iso = {!!}
                      }
    where inv : ∀ {A B}
              → Σ[ g ∈ G ] ρ (g , A) ≡ B
              → Σ[ g ∈ G ] ρ (g , B) ≡ A
          inv {A} {B} (g , ρA≡B) = g ⁻¹ , let open ≡-Reasoning in
            begin
              ρ (g ⁻¹ , B)
            ≡⟨ sym (cong (λ s → ρ (g ⁻¹ , s)) ρA≡B) ⟩
              ρ (g ⁻¹ , ρ (g , A))
            ≡⟨ sym compatibility ⟩
              ρ (g ⁻¹ ∙ g , A)
            ≡⟨ ρ-resp-≈ (proj₁ inverse g) ⟩
              ρ (ε , A)
            ≡⟨ identityA ⟩
              A
            ∎
