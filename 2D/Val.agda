{-# OPTIONS --without-K #-}

module 2D.Val where

open import Data.Integer as ℤ
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import 2D.Types
open import 2D.Iter
open import 2D.Sing
open import 2D.Power
open import 2D.SingIter

data Val : (τ : U) → Set where
  ⋆ :       Val 𝟙
  inl :     {τ₁ τ₂ : U} → Val τ₁ → Val (τ₁ ⊕ τ₂)
  inr :     {τ₁ τ₂ : U} → Val τ₂ → Val (τ₁ ⊕ τ₂)
  [_,_] :   {τ₁ τ₂ : U} → Val τ₁ → Val τ₂ → Val (τ₁ ⊗ τ₂)
  comb :    {τ : U} {p : τ ⟷ τ} → Iter p →  Val (# p)
  1/comb :  {τ : U} {p : τ ⟷ τ} → Sing p → Val (1/# p)
  𝟙ₚ :       {τ : U} {p q : τ ⟷ τ} → SingI {τ} {p} q  → Val (𝟙# p)

get-q : {t : U} {p : t ⟷ t} → Val (# p) → t ⟷ t
get-q (comb i) = Iter.q i

data _≈_ : {t : U} → Val t → Val t → Set where
  ⋆≈  : {e f : Val 𝟙} → e ≈ f
       -- programs are equivalent exactly when they are inverses
  #p≈ : ∀ {t} {p : t ⟷ t} (p^i p^j : Val (# p)) →
        get-q p^i ◎ ! (get-q p^j) ⇔ Prim id⟷ → p^i ≈ p^j
        -- p₁ and p₂ are equivalent, and there's order p proofs of that
        -- the "proof" is always easily done, but still expresses the right thing
        -- so it is best to have it instead of skipping it
  1/#p≈ : ∀ {t} {p : t ⟷ t}  (q : Iter p) → (p₁ p₂ : Sing p) →
        Sing.p' p₁ ◎ ! (Sing.p' p₂) ⇔ Iter.q q ◎ ! (Iter.q q) → (1/comb p₁) ≈ (1/comb p₂)
        -- all 𝟙ₚ are the same, even at different indices.
  𝟙ₚ≈ : ∀ {t} {p : t ⟷ t} (p₁ : t ⟷ t) {p₂ : t ⟷ t} (equiv : p₁ ⇔ p₂)
          {q : SingI {p = p} p₁} {r : SingI {p = p} p₂} → (𝟙ₚ q) ≈ (𝟙ₚ r)
  [,]≈ : {s t : U} {sv₁ sv₂ : Val s} {tv₁ tv₂ : Val t} → sv₁ ≈ sv₂ → tv₁ ≈ tv₂ → [ sv₁ , tv₁ ] ≈ [ sv₂ , tv₂ ]
  inj₁≈ : {s t : U} → {sv₁ sv₂ : Val s} → sv₁ ≈ sv₂ → inl {s} {t} sv₁ ≈ inl sv₂
  inj₂≈ : {s t : U} → {tv₁ tv₂ : Val t} → tv₁ ≈ tv₂ → inr {s} {t} tv₁ ≈ inr tv₂

get-equiv : ∀ {t} {p : t ⟷ t} {p^i p^j : Val (# p)} → p^i ≈ p^j → get-q p^i ◎ ! (get-q p^j) ⇔ Prim id⟷
get-equiv (#p≈ _ _ x) = x

refl≈ : ∀ {t} {v w : Val t} → v ≡ w → v ≈ w
refl≈ {v = ⋆} refl = ⋆≈
refl≈ {v = inl v} refl = inj₁≈ (refl≈ refl)
refl≈ {v = inr v} refl = inj₂≈ (refl≈ refl)
refl≈ {v = [ v , w ]} refl = [,]≈ (refl≈ refl) (refl≈ refl)
refl≈ {v = comb q } refl = #p≈ (comb q) (comb q) linv◎l
refl≈ {v = 1/comb {p = p} q} refl = 1/#p≈ (iter p) q q (linv◎l ● linv◎r)
refl≈ {v = 𝟙ₚ {p = p} {q} (si k eq) } refl = 𝟙ₚ≈ q id⇔

trans≈ : {t : U} → {a b c : Val t} → a ≈ b → b ≈ c → a ≈ c
trans≈ ⋆≈ ⋆≈ = ⋆≈
trans≈ (#p≈ p^i p^j x) (#p≈ .p^j p^j₁ x₁) =
  #p≈ p^i p^j₁ (2! (idl◎r ● (2! x) ⊡ (2! x₁) ● assoc◎l ● (assoc◎r ● (id⇔ ⊡ rinv◎l) ● idr◎l) ⊡ id⇔))
trans≈ (1/#p≈ q p₁ p₂ x) (1/#p≈ q₁ .p₂ p₃ x₁) =
  1/#p≈ q p₁ p₃ (2! (idr◎r ● ((2! x) ⊡ (id⇔ ● linv◎r ● 2! x₁)) ● assoc◎l ● (assoc◎r ● id⇔ ⊡ rinv◎l ● idr◎l) ⊡ id⇔  ))
trans≈ (𝟙ₚ≈ q eq₁) (𝟙ₚ≈ r eq₂) = 𝟙ₚ≈ q (eq₁ ● eq₂)
trans≈ ([,]≈ eq₁ eq₂) ([,]≈ eq₃ eq₄) = [,]≈ (trans≈ eq₁ eq₃) (trans≈ eq₂ eq₄)
trans≈ (inj₁≈ eq₁) (inj₁≈ eq₂) = inj₁≈ (trans≈ eq₁ eq₂)
trans≈ (inj₂≈ eq₁) (inj₂≈ eq₂) = inj₂≈ (trans≈ eq₁ eq₂)

sym≈ : {t : U} → {a b : Val t} → a ≈ b → b ≈ a
sym≈ ⋆≈ = ⋆≈
sym≈ (#p≈ (comb < k , q , α >) (comb < k₁ , q₁ , α₁ >) x) =
  #p≈ (comb < k₁ , q₁ , α₁ >) (comb < k , q , α > )
      ((!!⇔id q₁ ⊡ id⇔) ● ⇔! x)
sym≈ (1/#p≈ q p₁ p₂ x) = 1/#p≈ q p₂ p₁ ((sing⇔ p₂ p₁ ⊡ ⇔! (sing⇔ p₁ p₂)) ● x)
sym≈ (𝟙ₚ≈ q {p₂} eq) = 𝟙ₚ≈ p₂ (2! eq)
sym≈ ([,]≈ e₁ e₂) = [,]≈ (sym≈ e₁) (sym≈ e₂)
sym≈ (inj₁≈ e) = inj₁≈ (sym≈ e)
sym≈ (inj₂≈ e) = inj₂≈ (sym≈ e) 


