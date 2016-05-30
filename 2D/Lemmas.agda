module 2D.Lemmas where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty

open import 2D.Types
open import 2D.Pi

open import Relation.Binary.PropositionalEquality

ap∙ : {τ₁ τ₂ τ₃ : U} {v : El τ₁} (p₁ : τ₁ ⟷ τ₂) (p₂ : τ₂ ⟷ τ₃)
    → ap p₂ (ap p₁ v) ≡ ap (p₁ ◎ p₂) v
ap∙ unite₊l p₂ = refl
ap∙ uniti₊l p₂ = refl
ap∙ unite₊r p₂ = refl
ap∙ uniti₊r p₂ = refl
ap∙ swap₊ p₂ = refl
ap∙ assocl₊ p₂ = refl
ap∙ assocr₊ p₂ = refl
ap∙ unite⋆l p₂ = refl
ap∙ uniti⋆l p₂ = refl
ap∙ unite⋆r p₂ = refl
ap∙ uniti⋆r p₂ = refl
ap∙ swap⋆ p₂ = refl
ap∙ assocl⋆ p₂ = refl
ap∙ assocr⋆ p₂ = refl
ap∙ absorbr p₂ = refl
ap∙ absorbl p₂ = refl
ap∙ factorzr p₂ = refl
ap∙ factorzl p₂ = refl
ap∙ dist p₂ = refl
ap∙ factor p₂ = refl
ap∙ distl p₂ = refl
ap∙ factorl p₂ = refl
ap∙ id⟷ p₂ = refl
ap∙ (p₁ ◎ p₂) p₃ = refl
ap∙ (p₁ ⊕ p₂) p₃ = refl
ap∙ (p₁ ⊗ p₂) p₃ = refl

ap∼ : {τ : U} {v : El τ} {p₁ p₂ : τ ⟷ τ}
    → (p₁ ⇔ p₂) → ap p₁ v ≡ ap p₂ v
ap∼ assoc◎l = refl
ap∼ assoc◎r = refl
ap∼ idl◎l = refl
ap∼ idl◎r = refl
ap∼ idr◎l = refl
ap∼ idr◎r = refl
ap∼ id⇔ = refl
ap∼ (trans⇔ p₁ p₂) = trans (ap∼ p₁) (ap∼ p₂)
ap∼ (p₁ ⊡ p₂) = {!!}

!◎ : {τ₁ τ₂ τ₃ : U} (p₁ : τ₁ ⟷ τ₂) (p₂ : τ₂ ⟷ τ₃)
  → ! p₂ ◎ ! p₁ ⇔ ! (p₁ ◎ p₂)
!◎ unite₊l p₂ = id⇔
!◎ uniti₊l p₂ = id⇔
!◎ unite₊r p₂ = id⇔
!◎ uniti₊r p₂ = id⇔
!◎ swap₊ p₂ = id⇔
!◎ assocl₊ p₂ = id⇔
!◎ assocr₊ p₂ = id⇔
!◎ unite⋆l p₂ = id⇔
!◎ uniti⋆l p₂ = id⇔
!◎ unite⋆r p₂ = id⇔
!◎ uniti⋆r p₂ = id⇔
!◎ swap⋆ p₂ = id⇔
!◎ assocl⋆ p₂ = id⇔
!◎ assocr⋆ p₂ = id⇔
!◎ absorbr p₂ = id⇔
!◎ absorbl p₂ = id⇔
!◎ factorzr p₂ = id⇔
!◎ factorzl p₂ = id⇔
!◎ dist p₂ = id⇔
!◎ factor p₂ = id⇔
!◎ distl p₂ = id⇔
!◎ factorl p₂ = id⇔
!◎ id⟷ p₂ = id⇔
!◎ (p₁ ◎ p₂) p₃ = id⇔
!◎ (p₁ ⊕ p₂) p₃ = id⇔
!◎ (p₁ ⊗ p₂) p₃ = id⇔

!!⇔ : {τ₁ τ₂ : U} → (p : τ₁ ⟷ τ₂) → (! (! p) ⇔ p)
!!⇔ unite₊l = id⇔
!!⇔ uniti₊l = id⇔
!!⇔ unite₊r = id⇔
!!⇔ uniti₊r = id⇔
!!⇔ swap₊ = id⇔
!!⇔ assocl₊ = id⇔
!!⇔ assocr₊ = id⇔
!!⇔ unite⋆l = id⇔
!!⇔ uniti⋆l = id⇔
!!⇔ unite⋆r = id⇔
!!⇔ uniti⋆r = id⇔
!!⇔ swap⋆ = id⇔
!!⇔ assocl⋆ = id⇔
!!⇔ assocr⋆ = id⇔
!!⇔ absorbr = id⇔
!!⇔ absorbl = id⇔
!!⇔ factorzr = id⇔
!!⇔ factorzl = id⇔
!!⇔ dist = id⇔
!!⇔ factor = id⇔
!!⇔ distl = id⇔
!!⇔ factorl = id⇔
!!⇔ id⟷ = id⇔
!!⇔ (p₁ ◎ p₂) = (!!⇔ p₁) ⊡ (!!⇔ p₂)
!!⇔ (p₁ ⊕ p₂) = {!!}
!!⇔ (p₁ ⊗ p₂) = {!!}

⇔! : {τ₁ τ₂ : U} {p q : τ₁ ⟷ τ₂} → (p ⇔ q) → (! p ⇔ ! q)
⇔! assoc◎l = assoc◎r
⇔! assoc◎r = assoc◎l
⇔! idl◎l = idr◎l
⇔! idl◎r = idr◎r
⇔! idr◎l = idl◎l
⇔! idr◎r = idl◎r
⇔! id⇔ = id⇔
⇔! (trans⇔ q₁ q₂) = trans⇔ (⇔! q₁) (⇔! q₂)
⇔! (q₁ ⊡ q₂) = ⇔! q₂ ⊡ ⇔! q₁

ap⇔ : {τ : U} {v : El τ} {p₁ p₂ : τ ⟷ τ}
    → p₁ ⇔ p₂ → ap p₁ v ≡ ap p₂ v
ap⇔ assoc◎l = refl
ap⇔ assoc◎r = refl
ap⇔ idl◎l = refl
ap⇔ idl◎r = refl
ap⇔ idr◎l = refl
ap⇔ idr◎r = refl
ap⇔ id⇔ = refl
ap⇔ (trans⇔ q₁ q₂) = trans (ap⇔ q₁) (ap⇔ q₂)
ap⇔ (q₁ ⊡ q₂) = {!!}

ap!≡ : {τ : U} {v₁ v₂ : El τ} {p : τ ⟷ τ}
     → (ap p v₁ ≡ v₂) → (ap (! p) v₂ ≡ v₁)
ap!≡ {v₁ = inj₁ x} {p = swap₊} refl = refl
ap!≡ {v₁ = inj₂ y} {p = swap₊} refl = refl
ap!≡ {v₁ = proj₁ , proj₂} {p = swap⋆} refl = refl
ap!≡ {p = id⟷} refl = refl
ap!≡ {τ} {v₁ = v₁} {p = p₁ ◎ p₂} refl = trans (ap∙ (! p₂) (! p₁)) {!!}
ap!≡ {p = p₁ ⊕ p₂} refl = {!!}
ap!≡ {p = p₁ ⊗ p₂} refl = {!!}
