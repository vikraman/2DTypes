{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Pi2.Syntax where

infix 3 _⟷₁_ _⟷₂_ _⟷₃_
infix 5 !₁_ !₂_
infix 4 _◾₁_ _◾₂_

data U : Set where

  `𝟚 : ----
        U

data _⟷₁_ : U → U → Set where

  `id `not : -----------
             `𝟚 ⟷₁ `𝟚

  !₁_ : {A B : U} → (p : A ⟷₁ B)
      ----------------------------
      → (B ⟷₁ A)

  _◾₁_ : {A B C : U} → (p : A ⟷₁ B) (q : B ⟷₁ C)
       --------------------------------------------
       → (A ⟷₁ C)

`id₁ : {A : U} → A ⟷₁ A
`id₁ {`𝟚} = `id

data _⟷₂_ {A : U} : {B : U} (p q : A ⟷₁ B) → Set where

  `idl     : {B : U} (p : A ⟷₁ B)
           ----------------------
           → `id₁ ◾₁ p ⟷₂ p

  `idr     : {B : U} (p : A ⟷₁ B)
           ----------------------
           → p ◾₁ `id₁ ⟷₂ p

  `!l      : {B : U} (p : A ⟷₁ B)
           ----------------------
           → p ◾₁ !₁ p ⟷₂ `id₁

  `!r      : {B : U} (p : B ⟷₁ A)
           ----------------------
           → !₁ p ◾₁ p ⟷₂ `id₁

  `assoc   : {B C D : U} (p : A ⟷₁ B) (q : B ⟷₁ C) (r : C ⟷₁ D)
           ---------------------------------------------------------
           → (p ◾₁ q) ◾₁ r ⟷₂ p ◾₁ (q ◾₁ r)

!₂_ : {A B : U} {p q : A ⟷₁ B}
    → (u : p ⟷₂ q)
    ---------------------------------------------
    → q ⟷₂ p
!₂ u = {!!}

_◾₂_ : {A B : U} {p q r : A ⟷₁ B}
     → (u : p ⟷₂ q) (v : q ⟷₂ r)
     -------------------------------------------------------------
     → (p ⟷₂ r)
p ◾₂ q = {!!}

data _⟷₃_ {A B : U} {p q : A ⟷₁ B} (u v : p ⟷₂ q) : Set where

  `trunc : --------
           u ⟷₃ v

module Tests where

  !!₁ : {A B : U} → (p : A ⟷₁ B) → !₁ !₁ p ⟷₂ p
  !!₁ `id = {!!}
  !!₁ `not = {!!}
  !!₁ (!₁ p) = {!!}
  !!₁ (p ◾₁ p₁) = {!!}

  !not : !₁ `not ⟷₂ `not
  !not = {!!}

  !◾₁ : {A B C : U} → (p : A ⟷₁ B) (q : B ⟷₁ C) → !₁ (p ◾₁ q) ⟷₂ !₁ q ◾₁ !₁ p
  !◾₁ p q = {!!}

  ◾₁-assoc : {A B C D : U} → (p : A ⟷₁ B) (q : B ⟷₁ C) (r : C ⟷₁ D)
           → (p ◾₁ q) ◾₁ r ⟷₂ p ◾₁ (q ◾₁ r)
  ◾₁-assoc p q r = {!!}

  !!₂ : {A B : U} {p q : A ⟷₁ B} (u : p ⟷₂ q) → !₂ !₂ u ⟷₃ u
  !!₂ u = `trunc

  ◾₂-assoc : {A B : U} {p q r s : A ⟷₁ B}
           → (u : p ⟷₂ q) (v : q ⟷₂ r) (w : r ⟷₂ s)
           → (u ◾₂ v) ◾₂ w ⟷₃ u ◾₂ (v ◾₂ w)
  ◾₂-assoc u v w = `trunc

  ⟷₂-resp-◾₁ : {A B C : U} {p q : A ⟷₁ B} {r s : B ⟷₁ C}
               → (u : p ⟷₂ q) (v : r ⟷₂ s)
               → p ◾₁ r ⟷₂ q ◾₁ s
  ⟷₂-resp-◾₁ u v = {!!}
