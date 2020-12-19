{-# OPTIONS --without-K --exact-split #-}

module Pi+.Conjectures where

open import Pi+.Pi+ as Pi
open import Pi+.FSMG as FSMG

open import lib.Basics

M = FSMG Unit

-- eval
⟦_⟧₀ : U → M
⟦ O ⟧₀ = FSMG.I
⟦ U.I ⟧₀ = FSMG.η unit
⟦ X + Y ⟧₀ = ⟦ X ⟧₀ ⊗ ⟦ Y ⟧₀

⟦_⟧₁ : {X Y : U} → X ⟷ Y → ⟦ X ⟧₀ == ⟦ Y ⟧₀
⟦ p ⟧₁ = {!   !}

⟦_⟧₂ : {X Y : U} → {p q : X ⟷ Y } → p ⇔ q → ⟦ p ⟧₁ == ⟦ q ⟧₁
⟦_⟧₂ = {!   !}

-- quote
⌜_⌝₀ : M → U
⌜_⌝₀ = {!   !}