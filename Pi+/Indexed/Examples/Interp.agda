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

open import Pi+.Indexed.Examples.Base

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
encode O = ide ⊥
encode I = ⊔-comm ⊥ ⊤ ∘e Coprod-unit-l _ ⁻¹
encode (X + Y) = {!!}
encode (X × Y) = {!!}

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

open import Pi+.Indexed.Examples.Toffoli

test-interp-elems : _
test-interp-elems = interp-elems (toffoli 3)

test-interp-id : _
test-interp-id = interp-elems {t₁ = I + (I + I)} id⟷₁

{-
(true , true) ::
(inr true , inr true) :: (inr false , inr false) :: nil
-}

id+ : (I + I + I + O) Pi+.⟷₁ (I + I + I + O)
id+ = (Pi^.quote^₁ ∘ Pi^.quoteNorm₁ idp ∘ Pi^.evalNorm₁ ∘ eval₁) (id⟷₁ {t = I + (I + I)})

test-interp-id+ : _
test-interp-id+ = interp-elems {t₁ = (I + I + I + O)} id⟷₁

{-
(true , true) ::
(inr true , inr true) :: (inr (inr true) , inr (inr true)) :: nil
-}

idx : (I + I + I + I + I + I + O) Pi+.⟷₁ (I + I + I + I + I + I + O)
idx = (Pi^.quote^₁ ∘ Pi^.quoteNorm₁ idp ∘ Pi^.evalNorm₁ ∘ eval₁) (id⟷₁ {t = 𝟚 × (I + (I + I))})

test-interp-idx : _
test-interp-idx = interp-elems {t₁ = 𝟚 × (I + (I + I))} id⟷₁

{-
((true , true) , true , true) ::
((true , inr true) , true , inr true) ::
((true , inr false) , true , inr false) ::
((false , true) , false , true) ::
((false , inr true) , false , inr true) ::
((false , inr false) , false , inr false) :: nil

-------
a1,b1 a1,b2 a1,b3
-------
a2,b1 a2,b2, a2,b3

-}

test-interp-id+x : _
test-interp-id+x = interp-elems {t₁ = I + I + I + I + I + I + O} id⟷₁

{-
(true , true) ::
(inr true , inr true) ::
(inr (inr true) , inr (inr true)) ::
(inr (inr (inr true)) , inr (inr (inr true))) ::
(inr (inr (inr (inr true))) , inr (inr (inr (inr true)))) ::
(inr (inr (inr (inr (inr true)))) ,
 inr (inr (inr (inr (inr true)))))
:: nil

------
a1,b1 a1,b2 a1,b3
a2,b1 a2,b2 a2.b3

-}
