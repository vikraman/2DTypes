{-# OPTIONS --without-K --exact-split #-}

module Pi+.Conjectures1 where

open import Pi+.Pi+ as Pi

open import lib.Basics
open import lib.types.Fin
open import homotopy.FinSet

UFin = FinSet-exp

⟦_⟧₀ : U → UFin
⟦_⟧₀ = {!   !}

⌜_⌝₀ : UFin → U -- Pi : ℕ → U
⌜_⌝₀ = {!   !}

⌜⟦_⟧⌝₀ : {X : U} → ⌜ ⟦ X ⟧₀ ⌝₀ ⟷₁ X

⟦⌜_⌝⟧₀ : {X : UFin} → ⟦ ⌜ X ⌝₀ ⟧₀ == X

⟦_⟧₁ : {X Y : U} → X ⟷₁ Y → ⟦ X ⟧₀ == ⟦ Y ⟧₀
⟦ p ⟧₁ = {!   !}

{- lemma : {n : ℕ} → Fin n ≃ Fin n → Pi n ⟷ Pi n -}

⌜_⌝₁ : {X Y : UFin} → X == Y → ⌜ X ⌝₀ ⟷₁ ⌜ Y ⌝₀
⌜_⌝₁ = {!   !}

⌜⟦_⟧⌝₁ : ⌜ ⟦ p ⟧₀ ⌝₀ ⟷₂ p

⟦⌜_⌝⟧₁ : ⟦ ⌜ p ⌝₀ ⟧₀ == p


⟦_⟧₂ : {X Y : U} → {p q : X ⟷₁ Y } → p ⇔ q → ⟦ p ⟧₁ == ⟦ q ⟧₁
⟦ α ⟧₂ = {!   !}

⌜_⌝₂ : {X Y : UFin} {p q : X == Y} (α : p == q) → ⌜ p ⌝₁ ⟷₂ ⌜ q ⌝₁
⌜_⌝₂ = {!   !}

⟦⌜_⌝⟧₂ : ⟦ ⌜ α ⌝₂ ⟧₂ == α

⌜⟦_⟧⌝₂ : ⌜ ⟦ α ⟧₂ ⌝₂ ⟷₃ α
