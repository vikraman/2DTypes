{-# OPTIONS --rewriting --without-K --exact-split --overlapping-instances #-}

module Pi+.Lehmer.Lehmer2FinEquiv where

open import HoTT

open import Pi+.Misc
open import Pi+.Lehmer.FinHelpers
open import Pi+.Lehmer.Lehmer2

open import Pi+.UFin.BAut using (Aut)
open import Pi+.Extra

abstract
  instance
    Fin1-isProp : is-prop (Fin (S 0))
    Fin1-isProp = equiv-preserves-level {A = ⊥} TODO!

  AutFin1≃isContr : is-contr (Aut (Fin (S 0)))
  AutFin1≃isContr = inhab-prop-is-contr (ide (Fin (S 0)))

AutFin≃Lehmer-0 : Aut (Fin (S 0)) ≃ Lehmer 0
AutFin≃Lehmer-0 = TODO!
--   equiv (λ _ → tt) (λ _ → ide (Fin O))
--         (contr-has-all-paths _) (contr-has-all-paths _)

open import Pi+.Lehmer.FinHelpers

Fin≃Lehmer : {n : ℕ} -> Aut (Fin (S n)) ≃ Lehmer n
Fin≃Lehmer {O} = AutFin≃Lehmer-0
Fin≃Lehmer {S m} =
  Fin (S (S m)) ≃ Fin (S (S m)) ≃⟨ i ⟩
  Σ (Fin (S (S m))) (λ k → FinExcept fzero ≃ FinExcept k) ≃⟨ Σ-cong-equiv-snd ii ⟩
  Fin (S (S m)) × (Fin (S m) ≃ Fin (S m)) ≃⟨ _ , ×-isemap-r (Fin (S (S m))) (snd (Fin≃Lehmer {m})) ⟩
  Fin (S (S m)) × Lehmer m ≃∎
