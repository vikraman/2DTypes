{-# OPTIONS --rewriting --without-K --exact-split --overlapping-instances #-}

module Pi.Lehmer.Lehmer2FinEquiv where

open import HoTT hiding (_≤_; _<_; ≤-has-all-paths ; ltS ; ltSR)
import lib.types.Nat as N

open import Pi.Misc
open import Pi.Lehmer.FinHelpers
open import Pi.Lehmer.Lehmer2
open import Pi.Coxeter.InvTransform

open import Pi.UFin.BAut
open import Pi.Extra

open import Pi.Lehmer.FinHelpers

Fin≃Lehmer-aux : {n : ℕ} -> Aut (Fin (S n)) ≃ Lehmer n
Fin≃Lehmer-aux {O} =
  Aut (Fin (S O)) ≃⟨ contr-equiv-Unit (Aut-level {{Fin1-level}}) ⟩
  Unit ≃⟨ contr-equiv-Unit Fin1-level ⁻¹ ⟩
  Lehmer O ≃∎
Fin≃Lehmer-aux {S m} =
  Fin (S (S m)) ≃ Fin (S (S m)) ≃⟨ i ⟩
  Σ (Fin (S (S m))) (λ k → FinExcept fzero ≃ FinExcept k) ≃⟨ Σ-cong-equiv-snd ii ⟩
  Fin (S (S m)) × (Fin (S m) ≃ Fin (S m)) ≃⟨ _ , ×-isemap-r (Fin (S (S m))) (snd (Fin≃Lehmer-aux {m})) ⟩
  Fin (S (S m)) × Lehmer m ≃∎

Fin≃Lehmer : {n : ℕ} -> Aut (Fin (S n)) ≃ Lehmer n
Fin≃Lehmer = Fin≃Lehmer-aux ∘e inv-transform-equiv
