{-# OPTIONS --without-K #-}

module 2D.Val where

open import Relation.Binary.PropositionalEquality using (_≡_)

open import 2D.Types
open import 2D.Iter
open import 2D.Sing
open import 2D.Power

data Val : (τ : U) → Set where
  ⋆ :       Val 𝟙
  inl :     {τ₁ τ₂ : U} → Val τ₁ → Val (τ₁ ⊕ τ₂)
  inr :     {τ₁ τ₂ : U} → Val τ₂ → Val (τ₁ ⊕ τ₂)
  [_,_] :   {τ₁ τ₂ : U} → Val τ₁ → Val τ₂ → Val (τ₁ ⊗ τ₂)
  comb :    {τ : U} {p : τ ⟷ τ} → Iter p →  Val (# p)
  1/comb :  {τ : U} {p : τ ⟷ τ} → Sing p → Val (1/# p)
  𝟙ₚ :       {τ : U} {p : τ ⟷ τ} → Iter p → Val (𝟙# p)

-- need two more cases for ⊕
data _≈_ : {t : U} → Val t → Val t → Set where
  ⋆≈  : ⋆ ≈ ⋆
  #p≈ : ∀ {t} {p : t ⟷ t} {p^i p^j : Iter p} →
        p ◎ Iter.q p^i ⇔ Iter.q p^j ◎ p → (comb p^i) ≈ (comb p^j)
  1/#p≈ : ∀ {t} {p : t ⟷ t} {p₁ p₂ : Sing p} (q : Iter p) → (r : Iter p) →
        Iter.q q ◎ Sing.p' p₁ ⇔ Sing.p' p₂ ◎ Iter.q r → (1/comb p₁) ≈ (1/comb p₂)
  𝟙ₚ≈ : ∀ {t} {p : t ⟷ t} → (p₁ p₂ q r : Iter p) →
        Iter.q q ◎ Iter.q p₁ ⇔ Iter.q p₂ ◎ Iter.q r → (𝟙ₚ q) ≈ (𝟙ₚ r)
  [,]≈ : {s t : U} {sv₁ sv₂ : Val s} {tv₁ tv₂ : Val t} → sv₁ ≈ sv₂ → tv₁ ≈ tv₂ → [ sv₁ , tv₁ ] ≈ [ sv₂ , tv₂ ]
  inj₁≈ : {s t : U} → {sv₁ sv₂ : Val s} → sv₁ ≈ sv₂ → inl {s} {t} sv₁ ≈ inl sv₂
  inj₂≈ : {s t : U} → {tv₁ tv₂ : Val t} → tv₁ ≈ tv₂ → inr {s} {t} tv₁ ≈ inr tv₂
  
  -- this is rather useful in multiple instances
  refl≈ : ∀ {t} {v w : Val t} → v ≡ w → v ≈ w



