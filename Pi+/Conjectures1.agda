{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Conjectures1 where

open import Pi+.Pi+ as Pi
open import Pi+.UFin
open import Pi+.Syntax

-- open import HoTT
open import lib.Basics
-- open import lib.types.Fin

⟦_⟧₀ : U → UFin
⟦ O ⟧₀ = FinFS 0
⟦ I ⟧₀ = FinFS 1
⟦ x Pi.+ y ⟧₀ = ⟦ x ⟧₀ ∪ ⟦ y ⟧₀

⌜_⌝₀ : UFin → U -- Pi : ℕ → U
⌜ x ⌝₀ = ℕ→Pi (card x)

⌜⟦_⟧⌝₀ : (X : U) → ⌜ ⟦ X ⟧₀ ⌝₀ ⟷₁ X
⌜⟦ O ⟧⌝₀ = id⟷₁
⌜⟦ I ⟧⌝₀ = {!   !}
⌜⟦ X + X₁ ⟧⌝₀ = {!   !}

⟦⌜_⌝⟧₀ : (X : UFin) → ⟦ ⌜ X ⌝₀ ⟧₀ == X
⟦⌜ X ⌝⟧₀ = {!   !}

⟦_⟧₁ : {X Y : U} → X ⟷₁ Y → ⟦ X ⟧₀ == ⟦ Y ⟧₀ {- Lehmer n -}
⟦ p ⟧₁ = {!   !}

⌜_⌝₁ : {X Y : UFin} → X == Y → ⌜ X ⌝₀ ⟷₁ ⌜ Y ⌝₀
⌜_⌝₁ = {!   !}

-- ⌜⟦_⟧⌝₁ : {X Y : U} → (p : X ⟷₁ Y) → ⌜ ⟦ p ⟧₁ ⌝₁ ⟷₂ p
-- ⌜⟦ p ⟧⌝₁ = {!   !}

-- ⟦⌜_⌝⟧₁ : {X Y : UFin} → (p : X == Y) → ⟦ ⌜ p ⌝₁ ⟧₁ == p

⟦_⟧₂ : {X Y : U} → {p q : X ⟷₁ Y } → p ⟷₂ q → ⟦ p ⟧₁ == ⟦ q ⟧₁
⟦ α ⟧₂ = {!   !}

-- ⌜_⌝₂ : {X Y : UFin} {p q : X == Y} (α : p == q) → ⌜ p ⌝₁ ⟷₂ ⌜ q ⌝₁
-- ⌜ idp ⌝₂ = id⟷₂

-- ⟦⌜_⌝⟧₂ : {X Y : UFin} {p q : X == Y} (α : p == q) → ⟦ ⌜ α ⌝₂ ⟧₂ == α
-- ⟦⌜ α ⌝⟧₂ = prop-has-all-paths (ap ((⟦_⟧₁ ∘ ⌜_⌝₁)) α) ((ap ((⟦_⟧₁ ∘ ⌜_⌝₁)) α))

-- ⌜⟦_⟧⌝₂ : {X Y : UFin} {p q : X == Y} (α : p == q) → ⌜ ⟦ α ⟧₂ ⌝₂ ⟷₃ α
-- ⌜⟦ α ⟧⌝₂ = trunc
