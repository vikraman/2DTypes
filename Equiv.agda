{-# OPTIONS --without-K #-}

module Equiv where

open import Level using (_⊔_)
open import Function using (_∘_; id; flip)
open import Data.Sum renaming (map to _⊎→_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂) renaming (map to _×→_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

infix 4 _∼_
infix 4 _≃_
infixr 5 _●_

infix 8 _⊎≃_
infixr 7 _×≃_

------------------------------------------------------------------------------
-- Extensional equivalence of (unary) functions

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} → (f g : A → B) → Set (ℓ ⊔ ℓ')
_∼_ {A = A} f g = (x : A) → f x ≡ g x

refl∼ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} → (f ∼ f)
refl∼ _ = refl

sym∼ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g : A → B} → (f ∼ g) → (g ∼ f)
sym∼ H x = sym (H x)

trans∼ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g h : A → B} → (f ∼ g) → (g ∼ h) → (f ∼ h)
trans∼ H G x = trans (H x)  (G x)

∘-resp-∼ : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} {f h : B → C} {g i : A → B} →
  (f ∼ h) → (g ∼ i) → f ∘ g ∼ h ∘ i
∘-resp-∼ {f = f} {i = i} f∼h g∼i x = trans (cong f (g∼i x)) (f∼h (i x))

isEquivalence∼ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → IsEquivalence (_∼_ {ℓ} {ℓ′} {A} {B})
isEquivalence∼ = record { refl = refl∼ ; sym = sym∼ ; trans = trans∼ }

-- generally useful
cong∘l : ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″}
  {g i : A → B} → (f : B → C) →
  (g ∼ i) → (f ∘ g) ∼ (f ∘ i)
cong∘l f g~i x = cong f (g~i x)

cong∘r : ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″}
  {f h : B → C} → (g : A → B) →
  (f ∼ h) → (f ∘ g) ∼ (h ∘ g)
cong∘r g f~h x = f~h (g x)

------------------------------------------------------------------------------
-- Quasi-equivalences, in a more useful packaging
record _≃_ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor qeq
  field
    f : A → B
    g : B → A
    α : (f ∘ g) ∼ id
    β : (g ∘ f) ∼ id

-- We explicitly choose quasi-equivalences, even though these
-- these are not a proposition.  This is fine for us, as we're
-- explicitly looking at equivalences-of-equivalences, and we
-- so we prefer a symmetric definition over a truncated one.

id≃ : ∀ {ℓ} {A : Set ℓ} → A ≃ A
id≃ = qeq id id (λ _ → refl) (λ _ → refl)

sym≃ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → (A ≃ B) → B ≃ A
sym≃ (qeq f g α β) = qeq g f β α

abstract
  trans≃ :  ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} → A ≃ B → B ≃ C → A ≃ C
  trans≃ {A = A} {B} {C} (qeq f f⁻¹ fα fβ) (qeq g g⁻¹ gα gβ) =
    qeq (g ∘ f) (f⁻¹ ∘ g⁻¹) (λ x → trans (cong g (fα (g⁻¹ x))) (gα x))
                            (λ x → trans (cong f⁻¹ (gβ (f x))) (fβ x))
  -- more convenient infix version, flipped
  _●_ : ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} → B ≃ C → A ≃ B → A ≃ C
  _●_ = flip trans≃

  -- since we're abstract, these are all used to do restricted expansion
  β₁ : ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} {f : B ≃ C} {g : A ≃ B} →
    _≃_.f (f ● g) ∼ (_≃_.f f ∘ _≃_.f g)
  β₁ x = refl

  β₂ : ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} {f : B ≃ C} {g : A ≃ B} →
    _≃_.g (f ● g) ∼ _≃_.g g ∘ _≃_.g f
  β₂  x = refl

≃IsEquiv : IsEquivalence {Level.suc Level.zero} {Level.zero} {Set} _≃_
≃IsEquiv = record { refl = id≃ ; sym = sym≃ ; trans = trans≃ }

-- equivalences are injective

inj≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (eq : A ≃ B) → (x y : A) → (_≃_.f eq x ≡ _≃_.f eq y → x ≡ y)
inj≃ (qeq f g α β) x y p = trans
  (sym (β x)) (trans
  (cong g p) (
  β y))

-- equivalence is a congruence for plus/times

-- ⊕

abstract
  private
    _⊎∼_ : ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
      {f : A → C} {finv : C → A} {g : B → D} {ginv : D → B} →
      (α : f ∘ finv ∼ id) → (β : g ∘ ginv ∼ id) →
      (f ⊎→ g) ∘ (finv ⊎→ ginv) ∼ id {A = C ⊎ D}
    _⊎∼_ α β (inj₁ x) = cong inj₁ (α x)
    _⊎∼_ α β (inj₂ y) = cong inj₂ (β y)

  _⊎≃_ :  ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
    → A ≃ C → B ≃ D → (A ⊎ B) ≃ (C ⊎ D)
  (qeq fp gp αp βp) ⊎≃ (qeq fq gq αq βq) = qeq
    (Data.Sum.map fp fq)
    (Data.Sum.map gp gq)
    (αp ⊎∼ αq)
    (βp ⊎∼ βq)

  β⊎₁ : ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
    → {f : A ≃ C} → {g : B ≃ D} → _≃_.f (f ⊎≃ g) ∼ Data.Sum.map (_≃_.f f) (_≃_.f g)
  β⊎₁ _ = refl

  β⊎₂ : ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
    → {f : A ≃ C} → {g : B ≃ D} → _≃_.g (f ⊎≃ g) ∼ Data.Sum.map (_≃_.g f) (_≃_.g g)
  β⊎₂ _ = refl

-- ⊗

abstract
  private
    _×∼_ :  ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
      {f : A → C} {finv : C → A} {g : B → D} {ginv : D → B} →
      (α : f ∘ finv ∼ id) → (β : g ∘ ginv ∼ id) →
      (f ×→ g) ∘ (finv ×→ ginv) ∼ id {A = C × D}
    _×∼_ α β (x , y) = cong₂ _,_ (α x) (β y)

  _×≃_ :  ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
    → A ≃ C → B ≃ D → (A × B) ≃ (C × D)
  (qeq fp gp αp βp) ×≃ (qeq fq gq αq βq) = qeq
    (Data.Product.map fp fq)
    (gp ×→ gq)
    (_×∼_ {f = fp} {g = fq} αp αq)
    (_×∼_ {f = gp} {g = gq} βp βq)

  β×₁ : ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
    → {f : A ≃ C} → {g : B ≃ D} → _≃_.f (f ×≃ g) ∼ Data.Product.map (_≃_.f f) (_≃_.f g)
  β×₁ _ = refl

  β×₂ : ∀ {ℓA ℓB ℓC ℓD} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}  {D : Set ℓD}
    → {f : A ≃ C} → {g : B ≃ D} → _≃_.g (f ×≃ g) ∼ Data.Product.map (_≃_.g f) (_≃_.g g)
  β×₂ _ = refl

------------------------------------------------------------------------------
