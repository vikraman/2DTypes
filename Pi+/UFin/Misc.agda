{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

module Pi+.UFin.Misc where

open import HoTT hiding (transport-equiv)
open import Pi+.UFin.Univ

private
  variable
    i j k l : ULevel

prop-equiv : {A : Type i} {{_ : is-prop A}} {B : Type j} {{_ : is-prop B}}
           → (A → B) → (B → A) → A ≃ B
prop-equiv f g = equiv f g (λ _ → prop-has-all-paths _ _) (λ _ → prop-has-all-paths _ _)

contr-unit : {A : Type i} → (is-contr A) ≃ (A ≃ ⊤)
contr-unit = prop-equiv (λ ϕ → contr-center (≃-contr ϕ ⟨⟩)) (λ e → equiv-preserves-level (e ⁻¹))

module _ {i} {j} {A : Type i} where
  Σ₂-Lift-Unit : Σ A (λ _ → Lift {lzero} {j} Unit) ≃ A
  Σ₂-Lift-Unit = equiv fst (λ a → (a , lift unit)) (λ _ → idp) (λ { (a , lift tt) → idp })
