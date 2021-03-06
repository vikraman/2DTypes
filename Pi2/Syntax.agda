{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Pi2.Syntax where

open import Data.Bool

infix 3 _⟷₁_ _⟷₂_ _⟷₃_
infix 5 !₁_ !₂_
infix 4 _⊙₁_ _⊙₂_

------------------------------------------------------------------------------
-- Objects

data U : Set where

  `𝟚 : ----
        U

------------------------------------------------------------------------------
-- 1-paths

data _⟷₁_ : U → U → Set where

  `id : {A : U} →
        -----------
        A ⟷₁ A

  `not : -----------
        `𝟚 ⟷₁ `𝟚

  !₁_ : {A B : U} → (p : A ⟷₁ B)
      ----------------------------
      → (B ⟷₁ A)

  _⊙₁_ : {A B C : U} → (p : A ⟷₁ B) (q : B ⟷₁ C)
        --------------------------------------------
        → (A ⟷₁ C)

------------------------------------------------------------------------------
-- 2-paths

data _⟷₂_ : {A B : U} (p q : A ⟷₁ B) → Set where

  `id₂ : {A B : U} {p : A ⟷₁ B} →
         -------------------------
         p ⟷₂ p

  `idl     : {A B : U} (p : A ⟷₁ B)
           ----------------------
           → `id ⊙₁ p ⟷₂ p

  `idr     : {A B : U} (p : A ⟷₁ B)
           ----------------------
           → p ⊙₁ `id ⟷₂ p

  `!l      : {A B : U} (p : A ⟷₁ B)
           ----------------------
           → p ⊙₁ !₁ p ⟷₂ `id

  `!r      : {A B : U} (p : B ⟷₁ A)
           ----------------------
           → !₁ p ⊙₁ p ⟷₂ `id

  `!id    : {A : U} →
           -----------------------
           !₁ `id {A} ⟷₂ `id {A}

  `!not    :
           ----------------------
           !₁ `not ⟷₂ `not

  `!◾   : {A B C : U} {p : A ⟷₁ B} {q : B ⟷₁ C}
           -----------------------------------------
           → !₁ (p ⊙₁ q) ⟷₂ (!₁ q) ⊙₁ (!₁ p)

  `!!   : {A B : U} {p : A ⟷₁ B}
           -----------------------------------------
           → !₁ (!₁ p) ⟷₂ p

  `assoc   : {A B C D : U} (p : A ⟷₁ B) (q : B ⟷₁ C) (r : C ⟷₁ D)
           ---------------------------------------------------------
           → (p ⊙₁ q) ⊙₁ r ⟷₂ p ⊙₁ (q ⊙₁ r)

  `!       : {A B : U} {p q : A ⟷₁ B}
           → p ⟷₂ q
           ---------------------------
           → !₁ p ⟷₂ !₁ q

  !₂_      : {A B : U} {p q : A ⟷₁ B}
           → (u : p ⟷₂ q)
           --------------------------
           → q ⟷₂ p

  _⊙₂_   : {A B : U} {p q r : A ⟷₁ B}
          → (u : p ⟷₂ q) (v : q ⟷₂ r)
          --------------------------------
          → (p ⟷₂ r)

  _□₂_ : {A B C : U} {p q : A ⟷₁ B} {r s : B ⟷₁ C} (u : p ⟷₂ q) (v : r ⟷₂ s)
         --------------------------------------------------------------------------
         → (p ⊙₁ r) ⟷₂ (q ⊙₁ s)

------------------------------------------------------------------------------
-- n+3-paths for n ≥ 0

data _⟷₃_ {A B : U} {p q : A ⟷₁ B} (u v : p ⟷₂ q) : Set where

  `trunc : --------
           u ⟷₃ v

------------------------------------------------------------------------------
-- Op Semantics

El : U → Set
El `𝟚 = Bool

evalF : {A B : U} → (c : A ⟷₁ B) → El A → El B
evalB : {A B : U} → (c : A ⟷₁ B) → El B → El A

evalF `id v = v
evalF `not false = true
evalF `not true = false
evalF (!₁ c) v = evalB c v
evalF (c₁ ⊙₁ c₂) v = evalF c₂ (evalF c₁ v)

evalB `id v = v
evalB `not false = true
evalB `not true = false
evalB (!₁ c) v = evalF c v
evalB (c₁ ⊙₁ c₂) v = evalB c₁ (evalB c₂ v)

eval2F : {A B : U} {p q : A ⟷₁ B} → (u : p ⟷₂ q) → (El A → El B) → (El A → El B)
eval2F `id₂ f = f
eval2F (`idl p) f = f
eval2F (`idr p) f = f
eval2F (`!l p) f = {!!}
eval2F (`!r p) f = {!!}
eval2F `!id f = {!!}
eval2F `!not f = {!!}
eval2F `!◾ f = {!!}
eval2F `!! f = {!!}
eval2F (`assoc p q r) f = {!!}
eval2F (`! u) f = {!!}
eval2F (!₂ u) f = {!!}
eval2F (u ⊙₂ u₁) f = {!!}
eval2F (u □₂ u₁) f = {!!}

-- and so on and so forth??  Now the big question is how to connect this to the
-- model One idea is: evalF c v = w means that one of the fibers of path ⟦ c ⟧
-- starts at v and ends at w ????????

------------------------------------------------------------------------------
module Tests where

  !!₂ : {A B : U} {p q : A ⟷₁ B} (u : p ⟷₂ q) → !₂ !₂ u ⟷₃ u
  !!₂ u = `trunc

  ◾₂-assoc : {A B : U} {p q r s : A ⟷₁ B}
           → (u : p ⟷₂ q) (v : q ⟷₂ r) (w : r ⟷₂ s)
           → (u ⊙₂ v) ⊙₂ w ⟷₃ u ⊙₂ (v ⊙₂ w)
  ◾₂-assoc u v w = `trunc

------------------------------------------------------------------------------

not◾not⇔id : `not ⊙₁ `not ⟷₂ `id
not◾not⇔id = ((!₂ `!not) □₂ `id₂) ⊙₂ (`!r _⟷₁_.`not)
