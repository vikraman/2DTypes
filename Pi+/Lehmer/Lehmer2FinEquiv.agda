{-# OPTIONS --rewriting --without-K --exact-split --overlapping-instances #-}

module Pi+.Lehmer.Lehmer2FinEquiv where

open import HoTT hiding (_≤_; _<_; ≤-has-all-paths)

open import Pi+.Extra
open import Pi+.Lehmer.FinHelpers
open import Pi+.Lehmer.Lehmer2
open import Pi+.Common.InequalityEquiv
open import Pi+.Common.Arithmetic

open import Pi+.UFin.BAut using (Aut)
open import Pi+.Extra

abstract
  e= : ∀ {i} {X : Type i} {n : ℕ} {e₁ e₂ : Fin n ≃ X} → ((f : Fin n) → (–> e₁ f == –> e₂ f)) → e₁ == e₂
  e= h = pair= (λ= h) prop-has-all-paths-↓

  instance
    Fin0-isProp : is-prop (Fin 0)
    Fin0-isProp = equiv-preserves-level {A = ⊥} (Fin-equiv-Empty ⁻¹)

  AutFin0≃isContr : is-contr (Aut (Fin 0))
  AutFin0≃isContr = inhab-prop-is-contr (ide (Fin 0))

AutFin≃Lehmer-0 : Aut (Fin 0) ≃ Lehmer 0
AutFin≃Lehmer-0 =
  equiv (λ _ → tt) (λ _ → ide (Fin 0))
        (contr-has-all-paths _) (contr-has-all-paths _)

open import Pi+.Lehmer.FinHelpers

Fin≃Lehmer : {n : ℕ} -> Aut (Fin n) ≃ Lehmer n
Fin≃Lehmer {O} = AutFin≃Lehmer-0
Fin≃Lehmer {S n} =
  Fin (S n) ≃ Fin (S n) ≃⟨ i ⟩
  (Σ[ k ∈ Fin (S n) ] (FinExcept fzero ≃ FinExcept k)) ≃⟨ Σ-cong-equiv-snd ii ⟩
  Fin (S n) × (Fin n ≃ Fin n) ≃⟨ _ , ×-isemap-r (Fin (S n)) (snd (Fin≃Lehmer {n})) ⟩
  Fin (S n) × Lehmer n ≃∎
