{-# OPTIONS --without-K #-}

module Pi2 where

open import Relation.Nullary

infix 3 _⟷₁_ _⟷₂_ _⟷₃_
infix 5 !₁_ !₂_
infix 4 _◾₁_ _◾₂_

data U : Set where

  `𝟚 : ----
        U

data _⟷₁_ : U → U → Set where

  `id `not : -----------
             `𝟚 ⟷₁ `𝟚

-- !₁_ and _◾₁_ are 1-combinators but they have computation rules that hold
-- upto judgmental equality

!₁_ : {A B : U} → (p : A ⟷₁ B)
    ----------------------------
    → (B ⟷₁ A)
!₁ `id = `not
!₁ `not = `id

_◾₁_ : {A B C : U} → (p : A ⟷₁ B) (q : B ⟷₁ C)
     --------------------------------------------
     → (A ⟷₁ C)
`id ◾₁ `id = `id
`id ◾₁ `not = `not
`not ◾₁ `id = `not
`not ◾₁ `not = `id

data _⟷₂_ : {A B : U} (p q : A ⟷₁ B) → Set where

  `id      : {A B : U} → (p : A ⟷₁ B)
           ----------------------
           → p ⟷₂ p

-- !₂_ and _◾₂_ are 2-combinators but they have computation rules that hold
-- upto judgmental equality

!₂_ : {A B : U} {p q : A ⟷₁ B}
    → (u : p ⟷₂ q)
    ---------------------------------------------
    → q ⟷₂ p
!₂ `id p = `id p

_◾₂_ : {A B : U} {p q r : A ⟷₁ B}
     → (u : p ⟷₂ q) (v : q ⟷₂ r)
     -------------------------------------------------------------
     → (p ⟷₂ r)
`id p ◾₂ `id .p = `id p

data _⟷₃_ {A B : U} {p q : A ⟷₁ B} (u v : p ⟷₂ q) : Set where

  `trunc : --------
           u ⟷₃ v

module Tests where

  !!₁ : {A B : U} → (p : A ⟷₁ B) → !₁ !₁ p ⟷₂ p
  !!₁ `id = `id `id
  !!₁ `not = `id `not

  !not : ¬ (!₁ `not ⟷₂ `not)
  !not ()

  ◾₁-assoc : {A B C D : U} → (p : A ⟷₁ B) (q : B ⟷₁ C) (r : C ⟷₁ D)
           → (p ◾₁ q) ◾₁ r ⟷₂ p ◾₁ (q ◾₁ r)
  ◾₁-assoc `id `id `id = `id `id
  ◾₁-assoc `id `id `not = `id `not
  ◾₁-assoc `id `not `id = `id `not
  ◾₁-assoc `id `not `not = `id `id
  ◾₁-assoc `not `id `id = `id `not
  ◾₁-assoc `not `id `not = `id `id
  ◾₁-assoc `not `not `id = `id `id
  ◾₁-assoc `not `not `not = `id `not

  !!₂ : {A B : U} {p q : A ⟷₁ B} (u : p ⟷₂ q) → !₂ !₂ u ⟷₃ u
  !!₂ u = `trunc

  ◾₂-assoc : {A B : U} {p q r s : A ⟷₁ B}
           → (u : p ⟷₂ q) (v : q ⟷₂ r) (w : r ⟷₂ s)
           → (u ◾₂ v) ◾₂ w ⟷₃ u ◾₂ (v ◾₂ w)
  ◾₂-assoc u v w = `trunc
