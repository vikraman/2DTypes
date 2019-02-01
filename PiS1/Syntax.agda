{-# OPTIONS --without-K --rewriting #-}

module PiS1.Syntax where

data U : Set where
  S : U

infix 2 _⟷₁_

data _⟷₁_ : U → U → Set where
  id : S ⟷₁ S
  flip : S ⟷₁ S

infix 3 _⟷₂_

data _⟷₂_ {A B : U} (p : A ⟷₁ B) : A ⟷₁ B → Set where
  z : p ⟷₂ p
  s : (q : A ⟷₁ B) → p ⟷₂ q

open import HoTT

data Vec (A : Set) : ℕ → Set where
  [] : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (S n)

snocv : {A : Set} {n : ℕ} → Vec A n → A → Vec A (S n)
snocv [] a = a ∷ []
snocv (x ∷ xs) a = x ∷ snocv xs a

rot : {A : Set} {n : ℕ} → Vec A n → Vec A n
rot [] = []
rot (x ∷ xs) = snocv xs x

module _ {A : Set} {n : ℕ} where

  El : U → Set
  El S = Vec A n

  fwd : {A B : U} (p : A ⟷₁ B) → El A → El B
  fwd id x = x
  fwd flip x = rot x

  bwd : {A B : U} (p : A ⟷₁ B) → El B → El A
  bwd id x = x
  bwd flip x = x
