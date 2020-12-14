{-# OPTIONS --without-K --exact-split #-}

module Pi+.FSMG where

open import lib.Base
open import lib.types.Truncation

module _ {i} where
  postulate
    FSMG : (A : Type i) → Type i

  module _ {A : Type i} where
    infix 40 _⊗_
    postulate
      η : A → FSMG A
      I : FSMG A
      _⊗_ : FSMG A → FSMG A → FSMG A

      α : {X Y Z : FSMG A} → (X ⊗ Y) ⊗ Z == X ⊗ (Y ⊗ Z)
      Λ : {X : FSMG A} → I ⊗ X == X
      ρ : {X : FSMG A} → X ⊗ I == X
      β : {X Y : FSMG A} → X ⊗ Y == Y ⊗ X

      ⬠ : {W X Y Z : FSMG A}
        → α {W ⊗ X} {Y} {Z} ∙ α {W} {X} {Y ⊗ Z}
        == ap (_⊗ Z) (α {W} {X} {Y}) ∙ α {W} {X ⊗ Y} {Z} ∙ ap (W ⊗_) (α {X} {Y} {Z})
      ▽ : {X Y : FSMG A}
        → α {X} {I} {Y} ∙ ap (X ⊗_) (Λ {Y})
        == ap (_⊗ Y) (ρ {X})
      ⬡ : {X Y Z : FSMG A}
        → α {X} {Y} {Z} ∙ β {X} {Y ⊗ Z} ∙ α {Y} {Z} {X}
        == ap (_⊗ Z) (β {X} {Y}) ∙ α {Y} {X} {Z} ∙ ap (Y ⊗_) (β {X} {Z})

      β² : {X Y : FSMG A} → β {X} {Y} ∙ β {Y} {X} == idp

      trunc : Trunc 1 (FSMG A)
