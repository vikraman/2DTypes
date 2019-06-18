{-# OPTIONS --without-K #-}

module AutGroup where

open import lib.Basics
open import lib.NType2
open import lib.NConnected
open import lib.types.BAut
open import lib.types.Sigma
open import lib.types.Truncation

Aut : ∀ {i} → Type i → Type (lsucc i)
Aut A = A == A

pAut : ∀ {i} → Type i → Ptd (lsucc i)
de⊙ (pAut A) = Aut A
pt (pAut A) = idp

-- BAut : ∀ {i} → Type i → Type (lsucc i)
-- BAut {i} A = Σ (Type i) λ X → Trunc -1 (A == X)

-- pBAut : ∀ {i} → Type i → Ptd (lsucc i)
-- de⊙ (pBAut A) = BAut A
-- pt (pBAut A) = A , [ idp ]

EAut : ∀ {i} → Type i → Type (lsucc i)
EAut A = Σ (BAut A) λ X → fst X == A

pEAut : ∀ {i} → Type i → Ptd (lsucc i)
de⊙ (pEAut A) = EAut A
pt (pEAut A) = pt (pBAut A) , idp

instance
  EAut-contr : ∀ {i} {A : Type i} → is-contr (EAut A)
  EAut-contr {A = A} = has-level-in (pt (pEAut A) , EAut-contr-path) where
    trunc-path : (p : Trunc -1 (A == A)) → [ idp ] == p
    trunc-path = Trunc-elim λ q → prop-has-all-paths [ idp ] [ q ]
    EAut-contr-path : (X : EAut A) → (A , [ idp ]) , idp == X
    EAut-contr-path ((A , p) , idp) = pair= (pair= idp (trunc-path p)) {!!}

f : ∀ {i} {A : Type i} → Aut A → BAut A → EAut A
f p X@(A , q) = contr-center EAut-contr

-- if A is set, Aut A is set, so 0-connected
-- BAut A is 0-connected
-- hence Aut A × BAut A is 0-connected

g : ∀ {i} {A : Type i} → EAut A → Aut A × BAut A
g (X , p) = idp , X

f-g : ∀ {i} {A : Type i} (X : EAut A) → uncurry f (g X) == X
f-g X = contr-has-all-paths (uncurry f (g X)) X

-- g-f : ∀ {i} {A : Type i} (p : A == A) (X : BAut A) → g (f p X) == p , X
-- g-f p X@(A , q) = {!!}

g-f : ∀ {i} {A : Type i} (p : A == A) (X : BAut A) → [ g (f p X) ]₁ == [ p , X ]₁
g-f p X@(A , q) = Trunc-rec {{{!!}}} {!!} {!q!}

-- EAut : ∀ {i} → Type i → Type (lsucc i)
-- EAut {i} A = Σ (Type i) λ X → A == X

-- pEAut : ∀ {i} → Type i → Ptd (lsucc i)
-- de⊙ (pEAut A) = EAut A
-- pt (pEAut A) = A , idp

-- instance
--   EAut-contr : ∀ {i} {A : Type i} → is-contr (EAut A)
--   EAut-contr {A = A} = pathfrom-is-contr A

-- f : ∀ {i} {A : Type i} → Aut A → BAut A → EAut A
-- f p X@(A , q) = contr-center EAut-contr

-- g : ∀ {i} {A : Type i} → EAut A → Aut A × BAut A
-- g (X , p) = idp , X , [ p ]

-- f-g : ∀ {i} {A : Type i} (X : EAut A) → uncurry f (g X) == X
-- f-g X = contr-has-all-paths (uncurry f (g X)) X

-- -- if A is set, Aut A is set, so 0-connected
-- -- BAut A is 0-connected
-- -- hence Aut A × BAut A is 0-connected
-- -- path space is -1-connected

-- g-f : ∀ {i} {A : Type i} (p : A == A) (X : BAut A) → g (f p X) == p , X
-- g-f p X@(A , q) = {!!}
