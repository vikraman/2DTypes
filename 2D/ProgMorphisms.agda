{-# OPTIONS --without-K #-}

module 2D.ProgMorphisms where

open import Data.Product

open import 2D.Types
open import 2D.Sing
open import 2D.Iter
open import 2D.Power
open import 2D.Val

----------------------------------------------------------------------------
-- Note:  we don't need 'generic equivalences-of-equivalences' !
-- the operational semantics doesn't need them, and the denotational
-- semantics only needs each individual case

infix 4 _≡≈_

-- (no need for a constructor, as we should never see the insides of this
--  outside of this file.)
-- almost all cases are trivial, except for the 1/ case, at the end
data _≡≈_ : {τ : U} {p q : Val τ} (x y : p ≈ q) → Set where
  ⋆≡ : {p q : Val 𝟙} {e f : p ≈ q} → e ≡≈ f
  #p≡ : ∀ {t} {p : t ⟷ t} {p^i p^j : Val (# p)} {e f : p^i ≈ p^j} → e ≡≈ f
  [,]≡ : {s t : U} {v₁ v₂ : Val (s ⊗ t)} {e f : v₁ ≈ v₂} → e ≡≈ f
  inj≡ : {s t : U} → {v₁ v₂ : Val (s ⊕ t)} {e f : v₁ ≈ v₂} → e ≡≈ f
  tangr≡ : {t : U} {p q : t ⟷ t} {v₁ v₂ : Val (p // q)} {e f : v₁ ≈ v₂} → e ≡≈ f
  tangl≡ : {t : U} {p q : t ⟷ t} {v₁ v₂ : Val (q \\ p)} {e f : v₁ ≈ v₂} → e ≡≈ f


refl# : {τ : U} {p : τ ⟷ τ} {p q : Val τ} {eq : p ≈ q} → eq ≡≈ eq
refl# {eq = ⋆≈} = ⋆≡
refl# {eq = #p≈ x} = #p≡
refl# {eq = [,]≈ eq eq₁} = [,]≡
refl# {eq = inj≈ eq} = inj≡
refl# {eq = tangr≈} = tangr≡
refl# {eq = tangl≈} = tangl≡

sym# : {τ : U} {p : τ ⟷ τ} {p q : Val τ} {l r : p ≈ q} → l ≡≈ r → r ≡≈ l
sym# ⋆≡ = ⋆≡
sym# #p≡ = #p≡
sym# [,]≡ = [,]≡
sym# inj≡ = inj≡
sym# tangr≡ = tangr≡
sym# tangl≡ = tangl≡

trans# : {τ : U} {p q : Val τ} {i j k : p ≈ q} →
  i ≡≈ j → j ≡≈ k → i ≡≈ k
trans# {𝟘} () _
trans# {𝟙} ⋆≡ ⋆≡ = ⋆≡
trans# {τ₁ ⊕ τ₂} inj≡ inj≡ = inj≡
trans# {τ₁ ⊗ τ₂} [,]≡ [,]≡ = [,]≡
trans# {# x} #p≡ #p≡ = #p≡
trans# {p // q} tangr≡ tangr≡ = tangr≡
trans# {p \\ q} tangl≡ tangl≡ = tangl≡
