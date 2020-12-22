{-# OPTIONS --without-K --exact-split #-}

module Pi+.FSMG.Conjectures where

open import Pi+.Syntax as Pi
open import Pi+.FSMG.FSMG as FSMG

open import lib.Basics

M = FSMG Unit

-- eval
⟦_⟧₀ : U → M
⟦ O ⟧₀ = FSMG.I
⟦ U.I ⟧₀ = FSMG.η unit
⟦ X + Y ⟧₀ = ⟦ X ⟧₀ ⊗ ⟦ Y ⟧₀

⟦_⟧₁ : {X Y : U} → X ⟷₁ Y → ⟦ X ⟧₀ == ⟦ Y ⟧₀
⟦ p ⟧₁ = {!   !}

⟦_⟧₂ : {X Y : U} → {p q : X ⟷₁ Y } → p ⟷₂ q → ⟦ p ⟧₁ == ⟦ q ⟧₁
⟦_⟧₂ = {!   !}

-- quote
⌜_⌝₀ : M → U
⌜_⌝₀ = {!   !}
