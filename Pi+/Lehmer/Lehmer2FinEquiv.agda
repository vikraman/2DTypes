{-# OPTIONS --rewriting --without-K --exact-split --overlapping-instances #-}

module Pi+.Lehmer.Lehmer2FinEquiv where

open import HoTT

open import Pi+.Misc
open import Pi+.Lehmer.FinHelpers
open import Pi+.Lehmer.Lehmer2

open import Pi+.UFin.BAut
open import Pi+.Extra

AutFin≃Lehmer-0 : Aut (Fin (S 0)) ≃ Lehmer 0
AutFin≃Lehmer-0 = f , contr-to-contr-is-equiv f ⟨⟩ ⟨⟩
  where f : Aut (Fin (S 0)) → Lehmer 0
        f _ = 0 , ltS

open import Pi+.Lehmer.FinHelpers

Fin≃Lehmer : {n : ℕ} -> Aut (Fin (S n)) ≃ Lehmer n
Fin≃Lehmer {O} = AutFin≃Lehmer-0
Fin≃Lehmer {S m} =
  Fin (S (S m)) ≃ Fin (S (S m)) ≃⟨ i ⟩
  Σ (Fin (S (S m))) (λ k → FinExcept fzero ≃ FinExcept k) ≃⟨ Σ-cong-equiv-snd ii ⟩
  Fin (S (S m)) × (Fin (S m) ≃ Fin (S m)) ≃⟨ _ , ×-isemap-r (Fin (S (S m))) (snd (Fin≃Lehmer {m})) ⟩
  Fin (S (S m)) × Lehmer m ≃∎
