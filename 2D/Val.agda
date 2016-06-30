{-# OPTIONS --without-K #-}

module 2D.Val where

open import Data.Integer as ℤ
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import 2D.Types
open import 2D.Iter
open import 2D.Sing
open import 2D.Power
open import 2D.ProgMorphisms using (swapSI)

data Val : (τ : U) → Set where
  ⋆ :       Val 𝟙
  inl :     {τ₁ τ₂ : U} → Val τ₁ → Val (τ₁ ⊕ τ₂)
  inr :     {τ₁ τ₂ : U} → Val τ₂ → Val (τ₁ ⊕ τ₂)
  [_,_] :   {τ₁ τ₂ : U} → Val τ₁ → Val τ₂ → Val (τ₁ ⊗ τ₂)
  comb :    {τ : U} {p : τ ⟷ τ} → Iter p →  Val (# p)
  1/comb :  {τ : U} {p : τ ⟷ τ} → Sing p → Val (1/# p)
  𝟙ₚ :       {τ : U} {p : τ ⟷ τ} → Iter p → Val (𝟙# p)

data _≈_ : {t : U} → Val t → Val t → Set where
  ⋆≈  : ⋆ ≈ ⋆
       -- programs are equivalent exactly when they are inverses
  #p≈ : ∀ {t} {p : t ⟷ t} (p^i p^j : Iter p) →
        Iter.q p^i ◎ ! (Iter.q p^j) ⇔ Prim id⟷ → (comb p^i) ≈ (comb p^j)
        -- all proofs are equivalent, and there's order p of them
  1/#p≈ : ∀ {t} {p : t ⟷ t}  (q : Iter p) → (p₁ p₂ : Sing p) →
        Sing.p' p₁ ◎ ! (Sing.p' p₂) ⇔ Iter.q q ◎ ! (Iter.q q) → (1/comb p₁) ≈ (1/comb p₂)
        -- all are equivalent
  𝟙ₚ≈ : ∀ {t} {p : t ⟷ t} → (p₁ q r : Iter p) →
        (Iter.q q ◎ ! (Iter.q r)) ⇔ Iter.q p₁ → (𝟙ₚ q) ≈ (𝟙ₚ r)
  [,]≈ : {s t : U} {sv₁ sv₂ : Val s} {tv₁ tv₂ : Val t} → sv₁ ≈ sv₂ → tv₁ ≈ tv₂ → [ sv₁ , tv₁ ] ≈ [ sv₂ , tv₂ ]
  inj₁≈ : {s t : U} → {sv₁ sv₂ : Val s} → sv₁ ≈ sv₂ → inl {s} {t} sv₁ ≈ inl sv₂
  inj₂≈ : {s t : U} → {tv₁ tv₂ : Val t} → tv₁ ≈ tv₂ → inr {s} {t} tv₁ ≈ inr tv₂
  
refl≈ : ∀ {t} {v w : Val t} → v ≡ w → v ≈ w
refl≈ {v = ⋆} refl = ⋆≈
refl≈ {v = inl v} refl = inj₁≈ (refl≈ refl)
refl≈ {v = inr v} refl = inj₂≈ (refl≈ refl)
refl≈ {v = [ v , w ]} refl = [,]≈ (refl≈ refl) (refl≈ refl)
refl≈ {v = comb q } refl = #p≈ q q linv◎l
refl≈ {v = 1/comb {p = p} q} refl = 1/#p≈ (iter p) q q (linv◎l ● linv◎r)
refl≈ {v = 𝟙ₚ {p = p} < i , q , α > } refl =
  let ii = < i , q , α > in 𝟙ₚ≈ (zeroth p) ii ii linv◎l

trans≈ : {t : U} → {a b c : Val t} → a ≈ b → b ≈ c → a ≈ c
trans≈ ⋆≈ ⋆≈ = ⋆≈
trans≈ (#p≈ p^i p^j x) (#p≈ .p^j p^j₁ x₁) =
  #p≈ p^i p^j₁ (2! (idl◎r ● (2! x) ⊡ (2! x₁) ● assoc◎l ● (assoc◎r ● (id⇔ ⊡ rinv◎l) ● idr◎l) ⊡ id⇔))
trans≈ (1/#p≈ q p₁ p₂ x) (1/#p≈ q₁ .p₂ p₃ x₁) =
  1/#p≈ q p₁ p₃ (2! (idr◎r ● ((2! x) ⊡ (id⇔ ● linv◎r ● 2! x₁)) ● assoc◎l ● (assoc◎r ● id⇔ ⊡ rinv◎l ● idr◎l) ⊡ id⇔  ))
trans≈ (𝟙ₚ≈ {_} {p} < i , p₁ , α > q r x) (𝟙ₚ≈ < j , p₂ , β > .r r₁ x₁) =
  𝟙ₚ≈ < i ℤ.+ j , p₁ ◎ p₂ , α ⊡ β ● 2! (lower i j) > q r₁
       (2! ((2! x) ⊡ (2! x₁) ● assoc◎l ● ((assoc◎r ● id⇔ ⊡ rinv◎l ● idr◎l) ⊡ id⇔)))
trans≈ ([,]≈ eq₁ eq₂) ([,]≈ eq₃ eq₄) = [,]≈ (trans≈ eq₁ eq₃) (trans≈ eq₂ eq₄)
trans≈ (inj₁≈ eq₁) (inj₁≈ eq₂) = inj₁≈ (trans≈ eq₁ eq₂)
trans≈ (inj₂≈ eq₁) (inj₂≈ eq₂) = inj₂≈ (trans≈ eq₁ eq₂)

-- sym≈ : {t : U} → {a b : Val t} → a ≈ b → b ≈ a
-- sym≈ ⋆≈ = ⋆≈
-- sym≈ (#p≈ < k , q , α > < k₁ , q₁ , α₁ > x) =
--   #p≈ < k₁ , q₁ , α₁ > < k , q , α >
--       (α₁ ⊡ ⇔! α ● (id⇔ ⊡ 2! (^⇔! k) ● {!!}) ● x) 
-- sym≈ (1/#p≈ q p₁ p₂ x) = 1/#p≈ q p₂ p₁ ((sing⇔ p₂ p₁ ⊡ ⇔! (sing⇔ p₁ p₂)) ● x)
-- sym≈ (𝟙ₚ≈ p₁ q r x) = 𝟙ₚ≈ p₁ r q {!!}
-- sym≈ ([,]≈ e₁ e₂) = [,]≈ (sym≈ e₁) (sym≈ e₂)
-- sym≈ (inj₁≈ e) = inj₁≈ (sym≈ e)
-- sym≈ (inj₂≈ e) = inj₂≈ (sym≈ e) 

{--
α  : q ⇔ .p ^ k
α₁  : q₁ ⇔ .p ^ k₁
x  : q ◎ ! q₁ ⇔ Prim id⟷

?0 : q₁ ◎ ! q ⇔ q ◎ ! q₁

--}
