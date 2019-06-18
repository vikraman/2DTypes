{-# OPTIONS --cubical #-}

module scratch.Pi2 where

open import Cubical.Core.Everything
open import Cubical.Basics.Everything

_∘_ = compPath

data Pi2 : Set where
  b : Pi2
  n : b ≡ b
  n² : n ∘ n ≡ refl

notnotEq : notEq ∘ notEq ≡ refl
notnotEq = {!!}

El : Pi2 → Set
El b = Bool
El (n i) = notEq i
El (n² i j) = {!!}

coe : ∀ {i} {A B : Set i} → A ≡ B → A → B
coe p x = subst _ p x

coe! : ∀ {i} {A B : Set i} → A ≡ B → B → A
coe! p x = subst _ (sym p) x

fwd : b ≡ b → El b → El b
fwd p = coe λ i → El (p i)

bwd : b ≡ b → El b → El b
bwd p = coe! λ i → El (p i)

fwd∘bwd : (x : El b) (p : b ≡ b) → fwd p (bwd p x) ≡ x
fwd∘bwd x p = {!!}
