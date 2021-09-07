{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi.FSMG.SMG where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.PathOver
open import lib.PathGroupoid
open import lib.types.Truncation

open import Pi.FSMG.Paths
open import Pi.Common.Extra

record SMGStructure {i} (El : Type i) {{El-level : has-level 1 El}} : Type i where
  constructor smg-structure
  field
    I : El
    _⊗_ : El → El → El
  infix 40 _⊗_
  field
    α : {X Y Z : El} → (X ⊗ Y) ⊗ Z == X ⊗ (Y ⊗ Z)
    Λ : {X : El} → I ⊗ X == X
    ρ : {X : El} → X ⊗ I == X
    β : {X Y : El} → X ⊗ Y == Y ⊗ X

    ⬠ : {W X Y Z : El}
      → α {W ⊗ X} {Y} {Z} ∙ α {W} {X} {Y ⊗ Z}
      == ap (_⊗ Z) (α {W} {X} {Y}) ∙ α {W} {X ⊗ Y} {Z} ∙ ap (W ⊗_) (α {X} {Y} {Z})
    ▽ : {X Y : El}
      → α {X} {I} {Y} ∙ ap (X ⊗_) (Λ {Y})
      == ap (_⊗ Y) (ρ {X})
    ⬡ : {X Y Z : El}
      → α {X} {Y} {Z} ∙ β {X} {Y ⊗ Z} ∙ α {Y} {Z} {X}
      == ap (_⊗ Z) (β {X} {Y}) ∙ α {Y} {X} {Z} ∙ ap (Y ⊗_) (β {X} {Z})

    β² : {X Y : El} → β {X} {Y} ∙ β {Y} {X} == idp

record SMFunctor {i} {j} (A : Type i) {{_ : has-level 1 A}} {{GA : SMGStructure A}}
                         (B : Type j) {{_ : has-level 1 B}} {{GB : SMGStructure B}} : Type (lmax i j) where
  constructor sm-functor
  private
    module A = SMGStructure GA
    module B = SMGStructure GB
  field
    f : A → B
    f-I : f A.I == B.I
    f-⊗ : {X Y : A} → f (X A.⊗ Y) == f X B.⊗ f Y
  field
    f-α : {X Y Z : A}
        → ap f (A.α {X} {Y} {Z}) ∙ f-⊗ {X} {Y A.⊗ Z} ∙ ap (f X B.⊗_) (f-⊗ {Y} {Z})
        == f-⊗ {X A.⊗ Y} {Z} ∙ ap (B._⊗ f Z) (f-⊗ {X} {Y}) ∙ B.α {f X} {f Y} {f Z}
    f-Λ : {X : A} → ap f (A.Λ {X}) == f-⊗ {A.I} {X} ∙ ap (B._⊗ f X) f-I ∙ B.Λ {f X}
    f-ρ : {X : A} → ap f (A.ρ {X}) == f-⊗ {X} {A.I} ∙ ap (f X B.⊗_) f-I ∙ B.ρ {f X}
    f-β : {X Y : A} → ap f (A.β {X} {Y}) ∙ f-⊗ {Y} {X} == f-⊗ {X} {Y} ∙ B.β {f X} {f Y}

module _ {i j} {A : Type i} {{_ : has-level 1 A}} {{GA : SMGStructure A}}
               {B : Type j} {{_ : has-level 1 B}} {{GB : SMGStructure B}} where

  private
    module A = SMGStructure GA
    module B = SMGStructure GB

  sm-functor= : (F G : SMFunctor A B)
              → let module F = SMFunctor F ; module G = SMFunctor G in (p : F.f == G.f)
              → F.f-I == G.f-I [ (λ f → f A.I == B.I) ↓ p ]
              → ({X Y : A} → F.f-⊗ {X} {Y} == G.f-⊗ {X} {Y} [ (λ f → f (X A.⊗ Y) == f X B.⊗ f Y) ↓ p ])
              → F == G
  sm-functor= (sm-functor f f-I f-⊗ f-α f-Λ f-ρ f-β) (sm-functor g g-I g-⊗ g-α g-Λ g-ρ g-β) p ϕ ψ = TODO
