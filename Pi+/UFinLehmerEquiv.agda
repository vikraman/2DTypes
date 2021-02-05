{-# OPTIONS --without-K --rewriting #-}

module Pi+.UFinLehmerEquiv where

open import HoTT

open import Pi+.Lehmer.Lehmer
open import Pi+.Lehmer.LehmerFinEquiv
open import Pi+.Extra
open import Pi+.UFin

module _ {n : ℕ} where

    open import HoTT

    UFin≃BAut : Ω ⊙[ UFin , FinFS n ] ≃ ΩBAut (Fin n)
    UFin≃BAut = equiv f g f-g g-f
      where f : Ω ⊙[ UFin , FinFS n ] → ΩBAut (Fin n)
            f p = pair= (fst= p) prop-has-all-paths-↓
            g : ΩBAut (Fin n) → Ω ⊙[ UFin , FinFS n ]
            g p = pair= (fst= p) prop-has-all-paths-↓
            f-g : (p : ΩBAut (Fin n)) → f (g p) == p
            f-g p = TODO
            g-f : (p : Ω ⊙[ UFin , FinFS n ]) → g (f p) == p
            g-f p = TODO

    UFin≃Fin : Ω ⊙[ UFin , FinFS n ] ≃ Aut (Fin n)
    UFin≃Fin = Fin-loop-equiv n ∘e UFin≃BAut

module _ {n : ℕ} where

    UFin≃Lehmer : Ω ⊙[ UFin , FinFS (S n) ] ≃ Lehmer n
    UFin≃Lehmer = Fin≃Lehmer ∘e UFin≃Fin
