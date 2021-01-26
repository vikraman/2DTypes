{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

module Pi+.UFin.Univ where

open import HoTT

private
  variable
    i j : ULevel

-- TODO: we need a better definition of transport-equiv to compute it on fst
transport-equiv-fst :
  {P : Type i → Type j} {X Y : Type i} → (p : X == Y) →
  {ux : P X} {uy : P Y} → (up : ux == uy [ P ↓ p ]) →
  transport-equiv fst (pair= p up) == coe-equiv p
transport-equiv-fst idp idp = idp

is-univ-fib : {A : Type i} (B : A → Type j) → Type (lmax i j)
is-univ-fib B = ∀ {x y} → is-equiv (transport-equiv B {x} {y})

module _ (P : SubtypeProp (Type i) j) where

  open SubtypeProp P

  fib : Subtype P → Type i
  fib = fst

  fib-lift : (X Y : Subtype P) → (fib X == fib Y) → (X == Y)
  fib-lift X Y p = Subtype=-out P p

  fib-lift-equiv : (X Y : Subtype P) → (fib X == fib Y) ≃ (X == Y)
  fib-lift-equiv X Y = Subtype=-econv P X Y

  Subtype-is-univ : is-univ-fib fib
  Subtype-is-univ {X , ϕ} {Y , ψ} = is-eq f g f-g g-f
    where f : X , ϕ == Y , ψ → X ≃ Y
          f = transport-equiv fst
          g : X ≃ Y → X , ϕ == Y , ψ
          g e = –> (fib-lift-equiv (X , ϕ) (Y , ψ)) (ua e)
          f-g : (e : X ≃ Y) → f (g e) == e
          f-g e = transport-equiv-fst (ua e) (prop-has-all-paths-↓ {{level Y}}) ∙ coe-equiv-β e
          g-f : (p : X , ϕ == Y , ψ) → g (f p) == p
          g-f idp = pair== (ua-η idp) prop-has-all-paths-↓
            where instance _ = level X

open import homotopy.FinSet

FinSet-is-univ : is-univ-fib (fib FinSet-prop)
FinSet-is-univ = Subtype-is-univ FinSet-prop

FinSet-n-prop : (n : ℕ) → SubtypeProp Type₀ (lsucc lzero)
fst (FinSet-n-prop n) X = Σ ℕ λ n → Trunc -1 (Fin n == X)
snd (FinSet-n-prop n) X =
  all-paths-is-prop
    λ { (n , ϕ) (m , ψ) →
        pair= (Trunc-rec (λ p → Trunc-rec (λ q → Fin-inj n m (p ∙ ! q)) ψ) ϕ) prop-has-all-paths-↓ }

FinSet-n-is-univ : (n : ℕ) → is-univ-fib (fib (FinSet-n-prop n))
FinSet-n-is-univ n = Subtype-is-univ (FinSet-n-prop n)

BAut-is-univ : (A : Type i) → is-univ-fib (fib (BAut-prop A))
BAut-is-univ A = Subtype-is-univ (BAut-prop A)

FinSet-exp-is-univ : (n : ℕ) → is-univ-fib (fib (BAut-prop (Fin n)))
FinSet-exp-is-univ n = Subtype-is-univ (BAut-prop (Fin n))

UFin-is-univ = FinSet-is-univ
