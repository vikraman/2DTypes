{-# OPTIONS --without-K --exact-split #-}

module Pi+.Conjectures1 where

open import Pi+.Pi+ as Pi

open import lib.Basics
open import lib.types.Fin
open import homotopy.FinSet

UFin = FinSet-exp

⟦_⟧₀ : U → UFin
⟦_⟧₀ = ?

⟦_⟧₁ : {X Y : U} → X ⟷ Y → ⟦ X ⟧₀ == ⟦ Y ⟧₀
⟦ p ⟧₁ = ?

⟦_⟧₂ : {X Y : U} → {p q : X ⟷ Y } → p ⇔ q → ⟦ p ⟧₁ == ⟦ q ⟧₁
⟦ α ⟧₂ = ?