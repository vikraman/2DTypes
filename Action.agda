module _ where

open import Agda.Primitive
open import Algebra
open import Categories.Category
open import Categories.Groupoid
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.EqReasoning as EqR

record Action {c ℓ s} (G′ : Group c ℓ) (S : Set s) : Set (s ⊔ c ⊔ ℓ) where
  open Group G′ renaming (Carrier to G ; refl to ≈-refl ; sym to ≈-sym ; trans to ≈-trans)

  field
    ρ : G × S → S
    ρ-resp-≈ : ∀ {g g′ s} → g ≈ g′ → ρ (g , s) ≡ ρ (g′ , s)
    identityA : ∀ {x} → ρ (ε , x) ≡ x
    compatibility : ∀ {g h x} → ρ (g ∙ h , x) ≡ ρ (g , ρ (h , x))

  infix 4 _≋_
  data _≋_ {A B} (x y : Σ[ g ∈ G ] ρ (g , A) ≡ B) : Set ℓ where
    ≋> : .(proj₁ x ≈ proj₁ y) → x ≋ y

  ≋-isEquivalence : ∀ {A B} → IsEquivalence {A = Σ[ g ∈ G ] ρ (g , A) ≡ B} _≋_
  ≋-isEquivalence = record { refl = ≋> ≈-refl
                           ; sym = λ { (≋> p) → ≋> (≈-sym p) }
                           ; trans = λ { (≋> p) (≋> p′) → ≋> (≈-trans p p′) }
                           }

  ≋-setoid : ∀ {A B} → Setoid _ _
  ≋-setoid {A} {B} = record { Carrier = Σ[ g ∈ G ] ρ (g , A) ≡ B
                            ; _≈_ = _≋_
                            ; isEquivalence = ≋-isEquivalence
                            }

  ≋-cong : ∀ {A B} → {g g′ : G} → g ≈ g′
         → {p : ρ (g , A) ≡ B} → {p′ : ρ (g′ , A) ≡ B}
         → (g , p) ≋ (g′ , p′)
  ≋-cong p = ≋> p

  C : Category _ _ _
  C = record { Obj = S
             ; _⇒_ = λ s s′ → Σ[ g ∈ G ] ρ (g , s) ≡ s′
             ; _≡_ = _≋_
             ; id = ε , identityA
             ; _∘_ = _∘_
             ; assoc = {!!}
             ; identityˡ = identityˡ
             ; identityʳ = identityʳ
             ; equiv = ≋-isEquivalence
             ; ∘-resp-≡ = {!!}
             }
    where open Category C using (module HomReasoning)
          _∘_ : ∀ {A B C}
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
          identityˡ : ∀ {A B}
                    → {f : Σ[ g ∈ G ] ρ (g , A) ≡ B}
                    → (ε , identityA) ∘ f ≋ f
          identityˡ {f = (g , ρA≡B)} = let open EqR (≋-setoid) in
            begin
              (ε , identityA) ∘ (g , ρA≡B)
            ≡⟨ refl ⟩
              ε ∙ g , _
            ≈⟨ ≋-cong (proj₁ identity g) ⟩
              (g , ρA≡B)
            ∎
          identityʳ : ∀ {A B}
                    → {f : Σ[ g ∈ G ] ρ (g , A) ≡ B}
                    → f ∘ (ε , identityA) ≋ f
          identityʳ {f = (g , ρA≡B)} = let open EqR (≋-setoid) in
            begin
              (g , ρA≡B) ∘ (ε , identityA)
            ≡⟨ refl ⟩
              g ∙ ε , _
            ≈⟨ ≋-cong (proj₂ identity g) ⟩
              (g , ρA≡B)
            ∎
          .∘-resp-≋ : ∀ {A B C}
                   → {f h : Σ[ g ∈ G ] ρ (g , B) ≡ C}
                   → {g i : Σ[ g ∈ G ] ρ (g , A) ≡ B}
                   → f ≋ h → g ≋ i → f ∘ g ≋ h ∘ i
          ∘-resp-≋ {A} {B} {C} {f} {h} {g} {i} = let open HomReasoning in
            {!!}

  isGroupoid : Groupoid C
  isGroupoid = record { _⁻¹ = inv
                      ; iso = iso
                      }
    where open Category C using (_∘_ ; id)
          open import Categories.Morphisms C
          inv : ∀ {A B}
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
          isoˡ : ∀ {A B} {f : Σ[ g ∈ G ] ρ (g , A) ≡ B}
               → inv f ∘ f ≋ id
          isoˡ {f = g , ρA≡B} = let open EqR (≋-setoid) in
            begin
              inv (g , ρA≡B) ∘ (g , ρA≡B)
            ≡⟨ refl ⟩
              g ⁻¹ ∙ g , _
            ≈⟨ ≋-cong (proj₁ inverse g) ⟩
              ε , identityA
            ∎
          isoʳ : ∀ {A B} {f : Σ[ g ∈ G ] ρ (g , A) ≡ B}
               → f ∘ inv f ≋ id
          isoʳ {f = g , ρA≡B} = let open EqR (≋-setoid) in
            begin
              (g , ρA≡B) ∘ inv (g , ρA≡B)
            ≡⟨ refl ⟩
              g ∙ g ⁻¹ , _
            ≈⟨ ≋-cong (proj₂ inverse g) ⟩
              ε , identityA
            ∎
          iso : ∀ {A B} {f : Σ[ g ∈ G ] ρ (g , A) ≡ B}
              → Iso f (inv f)
          iso {f = f} = record { isoˡ = isoˡ {f = f} ; isoʳ = isoʳ {f = f} }
