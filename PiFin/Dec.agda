module PiFin.Dec where

open import IntensionalTypeTheory

data Dec {p} (P : Type p) : Type p where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

Decidable : ∀ {p r} {P : Type p} (R : P → P → Type r) → Type (p ⊔ r)
Decidable R = ∀ x y → Dec (R x y)
