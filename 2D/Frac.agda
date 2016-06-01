module 2D.Frac where

open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.Unit

infix 60 _⊗_
infix 50 _⊕_
infix 40 _⊘_
infix  30 _⟷_

mutual
  data U : Set where
    𝟘 : U
    𝟙 : U
    _⊕_ : U → U → U
    _⊗_ : U → U → U
    _⊘_ : (τ : U) → (τ ⟷ τ) → U

  data _⟷_ : U → U → Set where
    unite₊l :  {t : U} → 𝟘 ⊕ t ⟷ t
    uniti₊l :  {t : U} → t ⟷ 𝟘 ⊕ t
    unite₊r :  {t : U} → t ⊕ 𝟘 ⟷ t
    uniti₊r :  {t : U} → t ⟷ t ⊕ 𝟘
    swap₊   :  {t₁ t₂ : U} → (t₁ ⊕ t₂) ⟷ (t₂ ⊕ t₁)
    assocl₊ :  {t₁ t₂ t₃ : U} → t₁ ⊕ (t₂ ⊕ t₃) ⟷ (t₁ ⊕ t₂) ⊕ t₃
    assocr₊ :  {t₁ t₂ t₃ : U} → (t₁ ⊕ t₂) ⊕ t₃ ⟷ t₁ ⊕ (t₂ ⊕ t₃)
    unite⋆l :  {t : U} → 𝟙 ⊗ t ⟷ t
    uniti⋆l :  {t : U} → t ⟷ 𝟙 ⊗ t
    unite⋆r :  {t : U} → t ⊗ 𝟙 ⟷ t
    uniti⋆r :  {t : U} → t ⟷ t ⊗ 𝟙
    swap⋆   :  {t₁ t₂ : U} → t₁ ⊗ t₂ ⟷ t₂ ⊗ t₁
    assocl⋆ :  {t₁ t₂ t₃ : U} → t₁ ⊗ (t₂ ⊗ t₃) ⟷ (t₁ ⊗ t₂) ⊗ t₃
    assocr⋆ :  {t₁ t₂ t₃ : U} → (t₁ ⊗ t₂) ⊗ t₃ ⟷ t₁ ⊗ (t₂ ⊗ t₃)
    absorbr :  {t : U} → 𝟘 ⊗ t ⟷ 𝟘
    absorbl :  {t : U} → t ⊗ 𝟘 ⟷ 𝟘
    factorzr :  {t : U} → 𝟘 ⟷ t ⊗ 𝟘
    factorzl :  {t : U} → 𝟘 ⟷ 𝟘 ⊗ t
    dist :  {t₁ t₂ t₃ : U} → (t₁ ⊕ t₂) ⊗ t₃ ⟷ (t₁ ⊗ t₃) ⊕ (t₂ ⊗ t₃)
    factor :  {t₁ t₂ t₃ : U} → (t₁ ⊗ t₃) ⊕ (t₂ ⊗ t₃) ⟷ (t₁ ⊕ t₂) ⊗ t₃
    distl :  {t₁ t₂ t₃ : U} → t₁ ⊗ (t₂ ⊕ t₃) ⟷ (t₁ ⊗ t₂) ⊕ (t₁ ⊗ t₃)
    factorl :  {t₁ t₂ t₃ : U} → (t₁ ⊗ t₂) ⊕ (t₁ ⊗ t₃) ⟷ t₁ ⊗ (t₂ ⊕ t₃)
    id⟷ :  {t : U} → t ⟷ t
    _◎_ :  {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
    _⊕_ :  {t₁ t₂ t₃ t₄ : U} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ⊕ t₂ ⟷ t₃ ⊕ t₄)
    _⊗_ :  {t₁ t₂ t₃ t₄ : U} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ⊗ t₂ ⟷ t₃ ⊗ t₄)
    -- not complete

⟦_⟧ : U → Set
⟦ 𝟘 ⟧ = ⊥
⟦ 𝟙 ⟧ = ⊤
⟦ t₁ ⊕ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ t₁ ⊗ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
⟦ t ⊘ p ⟧ = {!!} -- a type whose elimination rule handles the nondeterminism

open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (+_)
open import Rational+ as ℚ

∣_∣ : U → ℚ
∣ 𝟘 ∣ = + 0 ÷ 1
∣ 𝟙 ∣ = + 1 ÷ 1
∣ t₁ ⊕ t₂ ∣ = ∣ t₁ ∣ + ∣ t₂ ∣
∣ t₁ ⊗ t₂ ∣ = ∣ t₁ ∣ * ∣ t₂ ∣
∣ t ⊘ p ∣ = {!!} -- ∣ t ∣ / order p

open import Universe

U-univ : Universe _ _
U-univ = record { U = U; El = ⟦_⟧ }
