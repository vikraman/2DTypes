{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Conjectures where

open import Pi+.Syntax as Pi
open import Pi+.UFin
open import Pi+.Level0

open import lib.Basics
open import lib.types.Fin
open import lib.types.Truncation
open import lib.NType2

⟦_⟧₀ : U → UFin
⟦ X ⟧₀ = FinFS ∣ X ∣

⌜_⌝₀ : UFin → U
⌜ X ⌝₀ = ⟪ card X ⟫

⌜⟦_⟧⌝₀ : (X : U) → ⌜ ⟦ X ⟧₀ ⌝₀ ⟷₁ X
⌜⟦ O ⟧⌝₀ = id⟷₁
⌜⟦ I ⟧⌝₀ = swap₊ ◎ unite₊l
⌜⟦ X + Y ⟧⌝₀ = !⟷₁ (normC (X + Y))

⟦⌜_⌝⟧₀ : (X : UFin) → Trunc -1 (⟦ ⌜ X ⌝₀ ⟧₀ == X)
⟦⌜_⌝⟧₀ = FinSet-elim-prop (λ _ → Trunc-level) λ n → [ pair= (ap Fin ∣⟪ n ⟫∣) prop-has-all-paths-↓ ]

-- ⟦_⟧₁ : {X Y : U} → X ⟷₁ Y → ⟦ X ⟧₀ == ⟦ Y ⟧₀ {- Lehmer n -}
-- ⟦ p ⟧₁ = {!   !}

-- ⌜_⌝₁ : {X Y : UFin} → X == Y → ⌜ X ⌝₀ ⟷₁ ⌜ Y ⌝₀
-- ⌜_⌝₁ = {!   !}

-- ⌜⟦_⟧⌝₁ : {X Y : U} → (p : X ⟷₁ Y) → ⌜ ⟦ p ⟧₁ ⌝₁ ⟷₂ p
-- ⌜⟦ p ⟧⌝₁ = {!   !}

-- ⟦⌜_⌝⟧₁ : {X Y : UFin} → (p : X == Y) → ⟦ ⌜ p ⌝₁ ⟧₁ == p

-- ⟦_⟧₂ : {X Y : U} → {p q : X ⟷₁ Y } → p ⟷₂ q → ⟦ p ⟧₁ == ⟦ q ⟧₁
-- ⟦ α ⟧₂ = {!   !}

-- ⌜_⌝₂ : {X Y : UFin} {p q : X == Y} (α : p == q) → ⌜ p ⌝₁ ⟷₂ ⌜ q ⌝₁
-- ⌜ idp ⌝₂ = id⟷₂

-- ⟦⌜_⌝⟧₂ : {X Y : UFin} {p q : X == Y} (α : p == q) → ⟦ ⌜ α ⌝₂ ⟧₂ == α
-- ⟦⌜ α ⌝⟧₂ = prop-has-all-paths (ap ((⟦_⟧₁ ∘ ⌜_⌝₁)) α) ((ap ((⟦_⟧₁ ∘ ⌜_⌝₁)) α))

-- ⌜⟦_⟧⌝₂ : {X Y : UFin} {p q : X == Y} (α : p == q) → ⌜ ⟦ α ⟧₂ ⌝₂ ⟷₃ α
-- ⌜⟦ α ⟧⌝₂ = trunc
