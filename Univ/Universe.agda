{-# OPTIONS --type-in-type --without-K #-}

module Univ.Universe where

open import Categories.Category
open import Categories.Functor
open import Categories.Adjunction
open import Univ.Cats

record Universe : Set where
  field
    -- types
    U   : Set
    -- contexts
    -- Con : U → Set
    Con : Set
    -- substitutions
    _↦_ : Con → Con → Set
    -- equivalence of substitutions
    _≣_  : {Γ Δ : Con} → Γ ↦ Δ → Γ ↦ Δ → Set

    instance ConIsCat : IsCategory Con _↦_ _≣_

  private module ConIsCat = IsCategory ConIsCat
  ConCat = ConIsCat.Cat

  field
    ModCat : Category _ _ _
    El  : Functor ConCat ModCat
    Lan : Functor ModCat ConCat
    adj : El ⊣ Lan
