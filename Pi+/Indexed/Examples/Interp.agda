{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

open import HoTT hiding (_<_ ; ltS ; ltSR ; _+_ ; _×_)
import lib.types.Nat as N
import lib.types.Sigma as S

open import Pi+.UFin.BAut
open import Pi+.Misc
open import Pi+.Extra

open import Pi+.Indexed.Syntax as Pi+
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.Indexed.SyntaxHatHelpers as Pi^
open import Pi+.Indexed.SyntaxFull as Pi
open import Pi+.Indexed.Translation
import Pi+.Indexed.Equiv1 as Pi+
import Pi+.Indexed.Equiv1Hat as Pi^
import Pi+.Indexed.Equiv0Norm as Pi^
import Pi+.Indexed.Equiv1Norm as Pi^
open import Pi+.UFin
open import Pi+.UFin.Monoidal
open import Pi+.Common.FinHelpers
open import Pi+.Lehmer.FinHelpers
open import Pi+.Indexed.Examples.Base using (⟦_⟧ ; ⟦-⟧-eval₀)

module Pi+.Indexed.Examples.Interp where

interp : {X Y : Pi.U} (c : X Pi.⟷₁ Y) -> ⟦ X ⟧ ≃ ⟦ Y ⟧
interp unite₊l = Coprod-unit-l _
interp uniti₊l = Coprod-unit-l _ ⁻¹
interp unite⋆l = ×₁-Unit _
interp uniti⋆l = ×₁-Unit _ ⁻¹
interp (swap₊ {t₁} {t₂}) = ⊔-comm ⟦ t₁ ⟧ ⟦ t₂ ⟧
interp (swap⋆ {t₁} {t₂}) = ×-comm {A = ⟦ t₁ ⟧} {⟦ t₂ ⟧}
interp assocl₊ = ⊔-assoc ⟦ _ ⟧ ⟦ _ ⟧ ⟦ _ ⟧ ⁻¹
interp assocr₊ = ⊔-assoc _ _ _
interp assocl⋆ = Σ-assoc ⁻¹
interp assocr⋆ = Σ-assoc
interp absorbr = ×₁-Empty _
interp absorbl = ×₁-Empty _ ∘e ×-comm
interp factorzr = (×₁-Empty _ ∘e ×-comm) ⁻¹
interp factorzl = ×₁-Empty _ ⁻¹
interp dist = ×-⊔-distrib _ _ _
interp factor = ×-⊔-distrib _ _ _ ⁻¹
interp id⟷₁ = ide _
interp (c₁ ◎ c₂) = interp c₂ ∘e interp c₁
interp (c₁ ⊕ c₂) = ⊔-≃ (interp c₁) (interp c₂)
interp (c₁ ⊗ c₂) = ×-≃ (interp c₁) (interp c₂)

-- sound : {X Y : Pi.U} (c : X Pi.⟷₁ Y)
--       → Pi^.evalNorm₁ (eval₁ c) ∘e ⟦-⟧-eval₀
--       == transport (λ n → ⟦ Y ⟧ ≃ Fin n)
--                    (! (eval₀-size c)) ⟦-⟧-eval₀ ∘e
--                    interp c

-- sound-test1 :
--   let c = swap₊ {t₁ = I + I + I} {t₂ = I + I} in
--   Pi^.evalNorm₁ (eval₁ c) ∘e ⟦-⟧-eval₀ ==  ⟦-⟧-eval₀ ∘e interp c
-- sound-test1 =
--   e= λ { (inl true) → idp ; (inl (inr true)) → idp ; (inl (inr false)) → idp ;
--          (inr (inl x)) → idp ; (inr (inr x)) → idp }

sound-test2 :
  let c = swap⋆ {t₁ = I + I} {t₂ = I + I} in
  Pi^.evalNorm₁ (eval₁ c) ∘e ⟦-⟧-eval₀ == ⟦-⟧-eval₀ ∘e interp c
sound-test2 =
  e= λ { (inl x , inl x₁) → idp ; (inl x , inr x₁) → idp ;
         (inr x , inl x₁) → idp ; (inr x , inr x₁) → idp }
