{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.FSMG.FSMG where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.PathOver
open import lib.PathGroupoid

open import Pi+.FSMG.Paths
open import Pi+.Extra

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

      β² : {X Y : FSMG A} → β {X} {Y} ∙ β {Y} {X} == idp {i} {FSMG A}

      instance trunc : has-level 1 (FSMG A)

    module FSMGElim {j} {P : FSMG A → Type j}
      (η* : (a : A) → P (η a))
      (I* : P I)
      (_⊗*_ : {X Y : FSMG A} → (X* : P X) → (Y* : P Y) → P (X ⊗ Y))
      (α* : {X Y Z : FSMG A} → {X* : P X} {Y* : P Y} {Z* : P Z} → ((X* ⊗* Y*) ⊗* Z*) == (X* ⊗* (Y* ⊗* Z*)) [ P ↓ α ])
      (Λ* : {X : FSMG A} {X* : P X} → (I* ⊗* X*) == X* [ P ↓ Λ ])
      (ρ* : {X : FSMG A} {X* : P X} → (X* ⊗* I*) == X* [ P ↓ ρ ])
      (β* : {X Y : FSMG A} {X* : P X} {Y* : P Y} → (X* ⊗* Y*) == (Y* ⊗* X*) [ P ↓ β ])
      (⬠* : {W X Y Z : FSMG A} {W* : P W} {X* : P X} {Y* : P Y} {Z* : P Z}
          → let p1 = α* {W ⊗ X} {Y} {Z} {W* ⊗* X*} {Y*} {Z*} ∙ᵈ α* {W} {X} {Y ⊗ Z} {W*} {X*} {Y* ⊗* Z*} in
            let p2 = $ (_⊗* Z*) (α* {W} {X} {Y} {W*} {X*} {Y*}) ∙ᵈ (α* {W} {X ⊗ Y} {Z} {W*} {X* ⊗* Y*} {Z*} ∙ᵈ $ (W* ⊗*_) (α* {X} {Y} {Z} {X*} {Y*} {Z*})) in
            p1 == p2 [ (λ p → (((W* ⊗* X*) ⊗* Y*) ⊗* Z*) == (W* ⊗* ((X* ⊗* (Y* ⊗* Z*)))) [ P ↓ p ]) ↓ ⬠ ])
      (▽* : {X Y : FSMG A} {X* : P X} {Y* : P Y}
          → let p1 = (α* {X} {I} {Y} {X*} {I*} {Y*} ∙ᵈ $ (X* ⊗*_) (Λ* {Y} {Y*})) in
            let p2 = $ (_⊗* Y*) (ρ* {X} {X*}) in
            p1 == p2 [ (λ p → ((X* ⊗* I*) ⊗* Y*) == (X* ⊗* Y*) [ P ↓ p ]) ↓ ▽ ])
      (⬡* : {X Y Z : FSMG A} {X* : P X} {Y* : P Y} {Z* : P Z}
          → let p1 = α* {X} {Y} {Z} {X*} {Y*} {Z*} ∙ᵈ (β* {X} {Y ⊗ Z} {X*} {Y* ⊗* Z*} ∙ᵈ α* {Y} {Z} {X} {Y*} {Z*} {X*}) in
            let p2 = $ (_⊗* Z*) (β* {X} {Y} {X*} {Y*}) ∙ᵈ (α* {Y} {X} {Z} {Y*} {X*} {Z*} ∙ᵈ $ (Y* ⊗*_) (β* {X} {Z} {X*} {Z*})) in
            p1 == p2 [ (λ p → ((X* ⊗* Y*) ⊗* Z*) == (Y* ⊗* (Z* ⊗* X*)) [ P ↓ p ]) ↓ ⬡ ])
      (β²* : {X Y : FSMG A} {X* : P X} {Y* : P Y}
           → (β* {X} {Y} {X*} {Y*} ∙ᵈ β* {Y} {X} {Y*} {X*}) == idp [ (λ p → (X* ⊗* Y*) == (X* ⊗* Y*) [ P ↓ p ]) ↓ β² ])
      (trunc* : {xs : FSMG A} → has-level 1 (P xs))
      where

      postulate
        f : (X : FSMG A) → P X
        f-η-β : {a : A} → f (η a) ↦ η* a
        {-# REWRITE f-η-β #-}
        f-I-β : f I ↦ I*
        {-# REWRITE f-I-β #-}
        f-⊗-β : {X Y : FSMG A} → f (X ⊗ Y) ↦ (f X ⊗* f Y)
        {-# REWRITE f-⊗-β #-}

      postulate
        f-α-β : {X Y Z : FSMG A} → apd f (α {X} {Y} {Z}) == α* {X} {Y} {Z} {f X} {f Y} {f Z}
        f-Λ-β : {X : FSMG A} → apd f (Λ {X}) == Λ* {X} {f X}
        f-ρ-β : {X : FSMG A} → apd f (ρ {X}) == ρ* {X} {f X}
        f-β-β : {X Y : FSMG A} → apd f (β {X} {Y}) == β* {X} {Y} {f X} {f Y}

    module FSMGElimSet {j} {P : FSMG A → Type j} {{trunc* : {X : FSMG A} → has-level 0 (P X)}}
      (η* : (a : A) → P (η a))
      (I* : P I)
      (_⊗*_ : {X Y : FSMG A} → (X* : P X) → (Y* : P Y) → P (X ⊗ Y))
      (α* : {X Y Z : FSMG A} → {X* : P X} {Y* : P Y} {Z* : P Z} → ((X* ⊗* Y*) ⊗* Z*) == (X* ⊗* (Y* ⊗* Z*)) [ P ↓ α ])
      (Λ* : {X : FSMG A} {X* : P X} → (I* ⊗* X*) == X* [ P ↓ Λ ])
      (ρ* : {X : FSMG A} {X* : P X} → (X* ⊗* I*) == X* [ P ↓ ρ ])
      (β* : {X Y : FSMG A} {X* : P X} {Y* : P Y} → (X* ⊗* Y*) == (Y* ⊗* X*) [ P ↓ β ])
      where

      private
        module E = FSMGElim {P = P} η* I* _⊗*_ α* Λ* ρ* β*
                   set-↓-has-all-paths-↓ set-↓-has-all-paths-↓ set-↓-has-all-paths-↓ set-↓-has-all-paths-↓
                   (raise-level 0 trunc*)

      f : (X : FSMG A) → P X
      f = E.f

    module FSMGRec {j} {P : Type j}
      (η* : (a : A) → P)
      (I* : P)
      (_⊗*_ : (X* : P) → (Y* : P) → P)
      (α* : {X* : P} {Y* : P} {Z* : P} → ((X* ⊗* Y*) ⊗* Z*) == (X* ⊗* (Y* ⊗* Z*)))
      (Λ* : {X* : P} → (I* ⊗* X*) == X*)
      (ρ* : {X* : P} → (X* ⊗* I*) == X*)
      (β* : {X* : P} {Y* : P} → (X* ⊗* Y*) == (Y* ⊗* X*))
      (⬠* : {W* : P} {X* : P} {Y* : P} {Z* : P}
          → α* {W* ⊗* X*} {Y*} {Z*} ∙ α* {W*} {X*} {Y* ⊗* Z*} == ap (_⊗* Z*) (α* {W*} {X*} {Y*}) ∙ (α* {W*} {X* ⊗* Y*} {Z*} ∙ ap (W* ⊗*_) (α* {X*} {Y*} {Z*})))
      (▽* : {X* : P} {Y* : P}
          → (α* {X*} {I*} {Y*} ∙ ap (X* ⊗*_) (Λ* {Y*})) == ap (_⊗* Y*) (ρ* {X*}))
      (⬡* : {X* : P} {Y* : P} {Z* : P}
          → α* {X*} {Y*} {Z*} ∙ (β* {X*} {Y* ⊗* Z*} ∙ α* {Y*} {Z*} {X*}) == ap (_⊗* Z*) (β* {X*} {Y*}) ∙ (α* {Y*} {X*} {Z*} ∙ ap (Y* ⊗*_) (β* {X*} {Z*})))
      (β²* : {X* : P} {Y* : P}
           → (β* {X*} {Y*} ∙ β* {Y*} {X*}) == idp)
      (trunc* : has-level 1 P)
      where

      private
        module E = FSMGElim {P = λ _ → P} η* I* _⊗*_ (↓-cst-in α*) (↓-cst-in Λ*) (↓-cst-in ρ*) (↓-cst-in β*) TODO TODO TODO TODO trunc*

      f : FSMG A → P
      f = E.f

      f-α-β : {X Y Z : FSMG A} → ap f (α {X} {Y} {Z}) == α* {f X} {f Y} {f Z}
      f-α-β = apd=cst-in E.f-α-β

      f-Λ-β : {X : FSMG A} → ap f (Λ {X}) == Λ* {f X}
      f-Λ-β = apd=cst-in E.f-Λ-β

      f-ρ-β : {X : FSMG A} → ap f (ρ {X}) == ρ* {f X}
      f-ρ-β = apd=cst-in E.f-ρ-β

      f-β-β : {X Y : FSMG A} → ap f (β {X} {Y}) == β* {f X} {f Y}
      f-β-β = apd=cst-in E.f-β-β
