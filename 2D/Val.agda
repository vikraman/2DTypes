{-# OPTIONS --without-K #-}

module 2D.Val where

open import Data.Integer as ℤ
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (Σ)

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
  tangr :   {τ : U} {p q : τ ⟷ τ} → ((r : Iter q) → Σ (Iter p) (λ s → Iter.q r ⇔ Iter.q s)) → Val (p // q)
  tangl :   {τ : U} {q p : τ ⟷ τ} → ((r : Iter q) → Σ (Iter p) (λ s → Iter.q r ⇔ Iter.q s)) → Val (q \\ p)

get-q : {t : U} {p : t ⟷ t} → Val (# p) → t ⟷ t
get-q (comb i) = Iter.q i

π₁ : {s t : U} → Val (s ⊗ t) → Val s
π₁ [ x , _ ] = x
π₂ : {s t : U} → Val (s ⊗ t) → Val t
π₂ [ _ , y ] = y

mutual
  inj-eq : {s t : U} (v₁ v₂ : Val (s ⊕ t)) → Set
  inj-eq (inl v) (inl w) = v ≈ w
  inj-eq (inl v) (inr w) = ⊥
  inj-eq (inr v) (inl w) = ⊥
  inj-eq (inr v) (inr w) = v ≈ w
  
  data _≈_ : {t : U} → Val t → Val t → Set where
    ⋆≈  : {e f : Val 𝟙} → e ≈ f
         -- programs are equivalent exactly when they are inverses
    #p≈ : ∀ {t} {p : t ⟷ t} (p^i p^j : Val (# p)) →
          get-q p^i ◎ ! (get-q p^j) ⇔ Prim id⟷ → p^i ≈ p^j
          -- p₁ and p₂ are equivalent, and there's order p proofs of that
          -- the "proof" is always easily done, but still expresses the right thing
          -- so it is best to have it instead of skipping it
    [,]≈ : {s t : U} {v₁ v₂ : Val (s ⊗ t)} → π₁ v₁ ≈ π₁ v₂ → π₂ v₁ ≈ π₂ v₂ → v₁ ≈ v₂
    inj≈ : {s t : U} → {v₁ v₂ : Val (s ⊕ t)} → inj-eq v₁ v₂ → v₁ ≈ v₂
    tangr≈ : {τ : U} {p q : τ ⟷ τ} → {f g : Val (p // q)} → f ≈ g
    tangl≈ : {τ : U} {q p : τ ⟷ τ} → {f g : Val (q \\ p)} → f ≈ g

get-equiv : ∀ {t} {p : t ⟷ t} {p^i p^j : Val (# p)} → p^i ≈ p^j → get-q p^i ◎ ! (get-q p^j) ⇔ Prim id⟷
get-equiv (#p≈ _ _ x) = x

refl≈ : ∀ {t} {v w : Val t} → v ≡ w → v ≈ w
refl≈ {v = ⋆} refl = ⋆≈
refl≈ {v = inl v} refl = inj≈ (refl≈ refl)
refl≈ {v = inr v} refl = inj≈ (refl≈ refl)
refl≈ {v = [ v , w ]} refl = [,]≈ (refl≈ refl) (refl≈ refl)
refl≈ {v = comb q } refl = #p≈ (comb q) (comb q) linv◎l
refl≈ {v = tangr f } refl = tangr≈
refl≈ {v = tangl f } refl = tangl≈

trans≈ : {t : U} → {a b c : Val t} → a ≈ b → b ≈ c → a ≈ c
trans≈ ⋆≈ ⋆≈ = ⋆≈
trans≈ (#p≈ p^i p^j x) (#p≈ .p^j p^j₁ x₁) =
  #p≈ p^i p^j₁ (2! (idl◎r ● (2! x) ⊡ (2! x₁) ● assoc◎l ● (assoc◎r ● (id⇔ ⊡ rinv◎l) ● idr◎l) ⊡ id⇔))
trans≈ ([,]≈ eq₁ eq₂) ([,]≈ eq₃ eq₄) = [,]≈ (trans≈ eq₁ eq₃) (trans≈ eq₂ eq₄)
trans≈ (inj≈ {v₁ = inl v₁} {inl v₂} eq₁) (inj≈ {v₂ = inl v₃} eq₂) = inj≈ (trans≈ eq₁ eq₂)
trans≈ (inj≈ {v₁ = inl v₁} {inl v₂} eq₁) (inj≈ {v₂ = inr v₃} ())
trans≈ (inj≈ {v₁ = inl v₁} {inr v₂} ()) (inj≈ eq₂)
trans≈ (inj≈ {v₁ = inr v₁} {inl v₂} ()) (inj≈ {v₂ = inl v₃} eq₂)
trans≈ (inj≈ {v₁ = inr v₁} {inr v₂} eq₁) (inj≈ {v₂ = inl v₃} ())
trans≈ (inj≈ {v₁ = inr v₁} {inl v₂} ()) (inj≈ {v₂ = inr v₃} eq₂)
trans≈ (inj≈ {v₁ = inr v₁} {inr v₂} eq₁) (inj≈ {v₂ = inr v₃} eq₂) = inj≈ (trans≈ eq₁ eq₂)
trans≈ (tangr≈) (tangr≈) = tangr≈
trans≈ (tangl≈) (tangl≈) = tangl≈

sym≈ : {t : U} → {a b : Val t} → a ≈ b → b ≈ a
sym≈ ⋆≈ = ⋆≈
sym≈ (#p≈ (comb < k , q , α >) (comb < k₁ , q₁ , α₁ >) x) =
  #p≈ (comb < k₁ , q₁ , α₁ >) (comb < k , q , α > )
      ((!!⇔id q₁ ⊡ id⇔) ● ⇔! x)
sym≈ ([,]≈ e₁ e₂) = [,]≈ (sym≈ e₁) (sym≈ e₂)
sym≈ (inj≈ {v₁ = inl v₁} {inl v₂} e) = inj≈ (sym≈ e)
sym≈ (inj≈ {v₁ = inl v₁} {inr v₂} ())
sym≈ (inj≈ {v₁ = inr v₁} {inl v₂} ())
sym≈ (inj≈ {v₁ = inr v₁} {inr v₂} e) = inj≈ (sym≈ e)
sym≈ (tangl≈) = tangl≈
sym≈ (tangr≈) = tangr≈

