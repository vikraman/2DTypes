{-# OPTIONS --without-K #-}

module 2D.Group where

open import Data.Unit
open import Data.Product
open import 2D.Types

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
open import Algebra.FunctionProperties
open import Algebra.Structures

open import Categories.Category
open import Categories.Groupoid

module _ {τ : U} (p : τ ⟷ τ) where

  postulate
    -- TODO
    ⇔-cong : {x y u v : τ ⟷ τ} → x ⇔ y → u ⇔ v → x ◎ u ⇔ y ◎ v

  EQ : IsEquivalence {A = τ ⟷ τ} _⇔_
  EQ = record { refl = id⇔ ; sym = 2! ; trans = _●_ }

  SG : IsSemigroup _⇔_ _◎_
  SG = record { isEquivalence = EQ
              ; assoc = λ x y z → assoc◎r
              ; ∙-cong = ⇔-cong
              }

  MON : IsMonoid _⇔_ _◎_ (Prim id⟷)
  MON = record { isSemigroup = SG
               ; identity = (λ _ → idl◎l) , (λ _ → idr◎l)
               }

  GRP : IsGroup _⇔_ _◎_ (Prim id⟷) !
  GRP = record { isMonoid = MON
               ; inverse = (λ _ → rinv◎l) , (λ _ → linv◎l)
               ; ⁻¹-cong = ⇔!
               }

module _ {a ℓ} {A : Set a} (≈ : Rel A ℓ)
         (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) (G : IsGroup ≈ _∙_ ε _⁻¹) where

  open IsGroup G
  -- open IsMonoid (IsGroup.isMonoid G)
  -- open IsSemigroup (IsMonoid.isSemigroup (IsGroup.isMonoid G))

  ≈-equiv : IsEquivalence ≈
  ≈-equiv = IsSemigroup.isEquivalence
              (IsMonoid.isSemigroup (IsGroup.isMonoid G))

  open IsEquivalence ≈-equiv

  DELOOP : Category _ _ _
  DELOOP = record { Obj = ⊤
                  ; _⇒_ = λ { tt tt → A }
                  ; _≡_ = ≈
                  ; id = ε
                  ; _∘_ = _∙_
                  ; assoc = λ {A₁} {B} {C} {D} {f} {g} {h} → assoc h g f
                  ; identityˡ = λ {A₁} {B} {f} → proj₁ identity f
                  ; identityʳ = λ {A₁} {B} {f} → proj₂ identity f
                  ; equiv = ≈-equiv
                  ; ∘-resp-≡ = λ {A₁} {B} {C} →
                                   IsSemigroup.∙-cong (IsMonoid.isSemigroup (IsGroup.isMonoid G))
                  }

  GRPD : Groupoid DELOOP
  GRPD = record { _⁻¹ = λ x → x ⁻¹
                ; iso = record { isoˡ = proj₁ inverse _
                               ; isoʳ = proj₂ inverse _
                               }
                }

  open import 2D.Circle

  LOOPSPACE : S¹ → A
  LOOPSPACE = rec-S¹ A ε P.refl

  ≈-setoid : Setoid _ _
  ≈-setoid = record { Carrier = A ; _≈_ = ≈
                    ; isEquivalence = ≈-equiv }

  open import Relation.Binary.EqReasoning (≈-setoid)

  LOOP : Category _ _ _
  LOOP = record { Obj = A
                ; _⇒_ = λ x y → ≈ x (((y ⁻¹) ∙ x) ∙ y)
                ; _≡_ = λ _ _ → ⊤
                ; id = λ {x} →
                  begin
                    x
                  ≈⟨ IsEquivalence.sym ≈-equiv (proj₁ identity x) ⟩
                    ε ∙ x
                  ≈⟨ IsEquivalence.sym ≈-equiv
                     (IsSemigroup.∙-cong (IsMonoid.isSemigroup (IsGroup.isMonoid G))
                                         (proj₁ inverse x) (IsEquivalence.refl ≈-equiv)) ⟩
                    ((x ⁻¹) ∙ x) ∙ x
                  ∎
                ; _∘_ = {!!} ; assoc = {!!}
                ; identityˡ = {!!}
                ; identityʳ = {!!}
                ; equiv = {!!}
                ; ∘-resp-≡ = {!!}
                }
