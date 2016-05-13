{-# OPTIONS --universe-polymorphism #-}
module Comonad where

open import Level

open import Categories.Category
open import Categories.Functor hiding (_≡_; assoc; identityˡ; identityʳ)
open import Categories.NaturalTransformation renaming (id to idN)

record Comonad {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  field
    F : Endofunctor (Category.op C)
    η : NaturalTransformation id F
    μ : NaturalTransformation (F ∘ F) F

  open Functor F

  field
    .assoc     : μ ∘₁ (F ∘ˡ μ) ≡ μ ∘₁ (μ ∘ʳ F)
    .identityˡ : μ ∘₁ (F ∘ˡ η) ≡ idN
    .identityʳ : μ ∘₁ (η ∘ʳ F) ≡ idN
