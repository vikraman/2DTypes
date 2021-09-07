{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

open import HoTT hiding (_<_ ; ltS ; ltSR ; _+_ ; _×_)
import lib.types.Nat as N
import lib.types.Sigma as S

open import Pi.UFin.BAut
open import Pi.Common.Misc
open import Pi.Common.Extra

open import Pi.Syntax.Pi+.Indexed as Pi+
open import Pi.Syntax.Pi^ as Pi^
open import Pi.Syntax.Pi^Helpers as Pi^
open import Pi.Syntax.Pi as Pi
open import Pi.Equiv.Translation2
import Pi.Equiv.Equiv1 as Pi+
import Pi.Equiv.Equiv1Hat as Pi^
import Pi.Equiv.Equiv0Norm as Pi^
import Pi.Equiv.Equiv1Norm as Pi^
open import Pi.UFin.UFin
open import Pi.UFin.Monoidal
open import Pi.Common.FinHelpers
open import Pi.Lehmer.FinExcept
open import Pi.Examples.Base using (⟦_⟧ ; ⟦-⟧-eval₀)

module Pi.Examples.Interp where

open import Pi.Examples.Base

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
interp distl = ⊔-≃ ×-comm ×-comm ∘e ×-⊔-distrib _ _ _ ∘e ×-comm
interp factor = ×-⊔-distrib _ _ _ ⁻¹
interp factorl = (⊔-≃ ×-comm ×-comm ∘e ×-⊔-distrib _ _ _ ∘e ×-comm) ⁻¹
interp id⟷₁ = ide _
interp (c₁ ◎ c₂) = interp c₂ ∘e interp c₁
interp (c₁ ⊕ c₂) = ⊔-≃ (interp c₁) (interp c₂)
interp (c₁ ⊗ c₂) = ×-≃ (interp c₁) (interp c₂)

interp+ : {n m : ℕ} {X : Pi+.U n} {Y : Pi+.U m} (c : X Pi+.⟷₁ Y) -> ⟦ X ⟧+ ≃ ⟦ Y ⟧+
interp+ unite₊l = Coprod-unit-l _
interp+ uniti₊l = Coprod-unit-l _ ⁻¹
interp+ (swap₊ {t₁ = t₁} {t₂ = t₂}) = ⊔-comm ⟦ t₁ ⟧+ ⟦ t₂ ⟧+
interp+ assocl₊ = ⊔-assoc ⟦ _ ⟧+ ⟦ _ ⟧+ ⟦ _ ⟧+ ⁻¹
interp+ assocr₊ = ⊔-assoc _ _ _
interp+ id⟷₁ = ide _
interp+ (c₁ ◎ c₂) = interp+ c₂ ∘e interp+ c₁
interp+ (c₁ ⊕ c₂) = ⊔-≃ (interp+ c₁) (interp+ c₂)

interp^ : {n m : ℕ} (c : n Pi^.⟷₁^ m) -> ⟦ n ⟧^ ≃ ⟦ m ⟧^
interp^ swap₊^ = ⊔-assoc ⊤ ⊤ _  ∘e ⊔-≃ (⊔-comm ⊤ ⊤) (ide _) ∘e ⊔-assoc ⊤ ⊤ _ ⁻¹
interp^ id⟷₁^ = ide _
interp^ (c₁ ◎^ c₂) = interp^ c₂ ∘e interp^ c₁
interp^ (⊕^ c) = ⊔-≃ (ide ⊤) (interp^ c)

encode : (X : Pi.U) → ⟦ X ⟧ ≃ ⟦ eval₀ X ⟧^
encode X =
    let r = ⟦-⟧-eval₀ {X}
        s = ⟦-⟧^-eval₀ {eval₀ X}
    in  s ⁻¹ ∘e r

elems : (t : Pi.U) → List ⟦ t ⟧
elems O = nil
elems I = tt :: nil
elems (t₁ + t₂) = map inl (elems t₁) ++ map inr (elems t₂)
elems (t₁ × t₂) = concat (map (λ v₁ → map (λ v₂ → (v₁ , v₂)) (elems t₂)) (elems t₁))

elems+ : ∀ {n} (t : Pi+.U n) → List ⟦ t ⟧+
elems+ O = nil
elems+ I = tt :: nil
elems+ (t₁ + t₂) = map inl (elems+ t₁) ++ map inr (elems+ t₂)

elems^ : ∀ n → List ⟦ n ⟧^
elems^ O = nil
elems^ (S n) = inl tt :: map inr (elems^ n)

test : _
test = elems (𝔹 3)

interp-elems : ∀ {t₁ t₂} (c : t₁ Pi.⟷₁ t₂) → List (⟦ t₁ ⟧ S.× ⟦ t₂ ⟧)
interp-elems {t₁ = t₁} c = map (λ v → (v , –> (interp c) v)) (elems t₁)

interp+-elems : ∀ {n m} {t₁ : Pi+.U n} {t₂ : Pi+.U m} (c : t₁ Pi+.⟷₁ t₂) → List (⟦ t₁ ⟧+ S.× ⟦ t₂ ⟧+)
interp+-elems {t₁ = t₁} c = map (λ v → (v , –> (interp+ c) v)) (elems+ t₁)

interp^-elems : ∀ {n m} (c : n Pi^.⟷₁^ m) → List (⟦ n ⟧^ S.× ⟦ m ⟧^)
interp^-elems {n = n} c = map (λ v → (v , –> (interp^ c) v)) (elems^ n)

encode-interp-elems : ∀ {t₁} {t₂} → ⟦ t₁ ⟧ S.× ⟦ t₂ ⟧ → ⟦ eval₀ t₁ ⟧^ S.× ⟦ eval₀ t₂ ⟧^
encode-interp-elems (v1 , v2) = (–> (encode _) v1) , (–> (encode _) v2)

open import Pi.Examples.Toffoli

id2 : 𝟚 Pi.× 𝟚 Pi.⟷₁ 𝟚 Pi.× 𝟚
id2 = toffoli 2

id2^ : _
id2^ = (Pi^.quote^₁ ∘ Pi^.quoteNorm₁ idp ∘ Pi^.evalNorm₁ ∘ eval₁) id2

test-interp-id2 = interp-elems id2
test-interp-id2+ = interp+-elems (Pi^.quote^₁ (eval₁ id2))
test-interp-id2^ = interp+-elems id2^

private
  x : _
  x = map encode-interp-elems test-interp-id2

sound-test1 :
  let c = swap₊ {t₁ = I + I + I} {t₂ = I + I} in
  (interp^-elems (Pi^.quoteNorm₁ idp (Pi^.evalNorm₁ (eval₁ c)))) == map encode-interp-elems (interp-elems c)
sound-test1 = idp

sound-test2 :
  let c = swap⋆ {t₁ = I + I} {t₂ = I + I} in
  Pi^.evalNorm₁ (eval₁ c) ∘e ⟦-⟧-eval₀ == ⟦-⟧-eval₀ ∘e interp c
sound-test2 =
  e= λ { (inl x , inl x₁) → idp ; (inl x , inr x₁) → idp ;
         (inr x , inl x₁) → idp ; (inr x , inr x₁) → idp }
