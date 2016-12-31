{-# OPTIONS --type-in-type --without-K #-}

module Univ.Universe where

open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_)
open import Univ.Cats

instance
  SetIsCat : IsCategory Set (λ A B → A → B) _==_
  SetIsCat =
    record { id = λ z → z
           ; _∘_ = λ g f x → g (f x)
           ; assoc = refl
           ; identityˡ = refl
           ; identityʳ = refl
           ; equiv = isEquivalence
           ; ∘-resp-≡ = λ { refl refl → refl }
           }

record Universe : Set where
  field
    -- codes
    U   : Set
    -- decoding a code to a space
    El  : U → Set
    -- the type of functions from spaces to spaces
    Fun : (A B : U) → Set
    -- homotopy of functions from spaces to spaces
    _∼_ : {A B : U} (f g : Fun A B) → Set

    -- identity relation on points in a space
    _≡_ : {A : U} (a b : El A) → Set
    -- equivalence of spaces El A and El B
    _≃_ : (A B : U) → Set

    instance
      SynCat : IsCategory U Fun _∼_
      ElFunc : IsFunctor ⦃ CIsCat = SynCat ⦄ ⦃ DIsCat = SetIsCat ⦄ El

  open IsCategory SynCat public
  open IsFunctor ElFunc public
