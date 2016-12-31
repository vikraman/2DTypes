{-# OPTIONS --type-in-type --without-K #-}

module Univ.IdSystem where

open import Level
open import Relation.Binary.PropositionalEquality
open import Univ.Universe

record IdSystem (A : Set) : Set where
  field
    R : A → A → Set
    r₀ : (a : A) → R a a
    f : (D : (a b : A) → R a b → Set)
      → (d : (a : A) → D a a (r₀ a))
      → (a b : A) (r : R a b)
      → D a b r
    η : (D : (a b : A) → R a b → Set)
      → (d : (a : A) → D a a (r₀ a))
      → (a : A)
      → f D d a a (r₀ a) ≡ d a

record Univalent (Univ : Universe) : Set where
  open Univ.Universe.Universe Univ
  field
    id-sys : IdSystem U
