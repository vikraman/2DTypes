module PiFin.List where

open import IntensionalTypeTheory

infixr 40 _∷_

data List (A : Type₀) : ℕ → Type₀ where
  []  : List A 0
  _∷_ : ∀ {n} → A → List A n → List A (succ n)

open import PiFin.Fin

fin-down : ∀ {A : Type₀} {n} → (Fin (succ n) → A) → Fin n → A
fin-down f x = f (fsucc x)

fin-out : ∀ {A : Type₀} {n} → (Fin n → A) → List A n
fin-out {n = zero} f = []
fin-out {n = succ n} f = f fzero ∷ fin-out (fin-down f)

fin-in : ∀ {A : Type₀} {n} → List A n → Fin n → A
fin-in (x ∷ xs) fzero = x
fin-in (x ∷ xs) (fsucc f) = fin-in xs f

fin-in-out : ∀ {n A} (f : Fin n → A) (x : Fin n) → fin-in (fin-out f) x == f x
fin-in-out {zero}   f ()
fin-in-out {succ n} f fzero = refl (f fzero)
fin-in-out {succ n} f (fsucc x) = fin-in-out (fin-down f) x

fin-up : ∀ {A : Type₀} {n} → (Fin n → A) → A → Fin (succ n) → A
fin-up f a fzero = a
fin-up f a (fsucc x) = f x

fin-out-in : ∀ {A n} (xs : List A n) → fin-out (fin-in xs) == xs
fin-out-in [] = refl []
fin-out-in (x ∷ xs) = ap (_∷_ x) (fin-out-in xs)

open import FunctionExtensionality

fin-list-equiv : ∀ {A n} → (Fin n → A) ≃ List A n
fin-list-equiv = fin-out , qinv-is-equiv (fin-in , (funext ∘ fin-in-out) , fin-out-in)
