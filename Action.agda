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
                hiding (isEquivalence)
  field
    ρ : G × S → S
    ρ-resp-≈ : ∀ {g g′ s} → g ≈ g′ → ρ (g , s) ≡ ρ (g′ , s)
    identityA : ∀ {x} → ρ (ε , x) ≡ x
    compatibility : ∀ {g h x} → ρ (g ∙ h , x) ≡ ρ (g , ρ (h , x))

  infix 4 _≋_
  _≋_ : ∀ {A B} → Rel (Σ[ g ∈ G ] ρ (g , A) ≡ B) ℓ
  (g , _) ≋ (g′ , _) = g ≈ g′

  ≋-isEquivalence : ∀ {A B} → IsEquivalence {A = Σ[ g ∈ G ] ρ (g , A) ≡ B} _≋_
  ≋-isEquivalence = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }

  ≋-setoid : ∀ {A B} → Setoid _ _
  ≋-setoid {A} {B} = record { Carrier = Σ[ g ∈ G ] ρ (g , A) ≡ B
                            ; _≈_ = _≋_
                            ; isEquivalence = ≋-isEquivalence
                            }

  ≋-cong : ∀ {A B} (f : Σ[ g ∈ G ] ρ (g , A) ≡ B → Σ[ g ∈ G ] ρ (g , A) ≡ B)
         → {x y : Σ[ g ∈ G ] ρ (g , A) ≡ B}
         → x ≋ y
         → f x ≋ f y
  ≋-cong {A} {B} f {(g , ρA≡B)} {(g′ , ρA≡B′)} p = {!!}

  C : Category _ _ _
  C = record { Obj = S
             ; _⇒_ = λ s s′ → Σ[ g ∈ G ] ρ (g , s) ≡ s′
             ; _≡_ = _≋_
             ; id = ε , identityA
             ; _∘_ = _∘_
             ; assoc = {!!}
             ; identityˡ = {!!}
             ; identityʳ = {!!}
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
          identityˡ {A} {B} {(g , ρA≡B)} = let open EqR (≋-setoid {A} {B}) in
            begin
              (ε , identityA) ∘ (g , ρA≡B)
            ≡⟨ refl ⟩
              ε ∙ g , _
            ≡⟨ {!!} ⟩
              (g , ρA≡B)
            ∎
          identityʳ : ∀ {A B}
                    → {f : Σ[ g ∈ G ] ρ (g , A) ≡ B}
                    → f ∘ (ε , identityA) ≋ f
          identityʳ {A} {B} {(g , ρA≡B)} = let open EqR (≋-setoid {A} {B}) in
            begin
              (g , ρA≡B) ∘ (ε , identityA)
            ≡⟨ refl ⟩
              g ∙ ε , _
            ≡⟨ {!!} ⟩
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
                      ; iso = record { isoˡ = {!!} ; isoʳ = {!!} }
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
          isoˡ : ∀ {A B}
               → {f : Σ[ g ∈ G ] ρ (g , A) ≡ B}
               → inv f ∘ f ≋ id
          isoˡ {A} {B} {g , ρA≡B} = let open EqR (≋-setoid) in
            begin
              inv (g , ρA≡B) ∘ (g , ρA≡B)
            ≡⟨ refl ⟩
              g ⁻¹ ∙ g , _
            ≡⟨ {!!} ⟩
              ε , identityA
            ∎
          isoʳ : ∀ {A B}
               → {f : Σ[ g ∈ G ] ρ (g , A) ≡ B}
               → f ∘ inv f ≋ id
          isoʳ {A} {B} {g , ρA≡B} = let open EqR (≋-setoid) in
            begin
              (g , ρA≡B) ∘ inv (g , ρA≡B)
            ≡⟨ refl ⟩
              g ∙ g ⁻¹ , _
            ≡⟨ {!!} ⟩
              ε , identityA
            ∎
