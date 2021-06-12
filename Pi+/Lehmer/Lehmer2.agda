{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

module Pi+.Lehmer.Lehmer2 where

open import HoTT

Lehmer : ℕ → Type₀
Lehmer O = ⊤
Lehmer (S n) = Fin (S n) × Lehmer n

open import Pi+.Lehmer.Lehmer renaming (Lehmer to Lehmer1)
open import Pi+.Lehmer.LehmerLevel
open import Pi+.Lehmer.LehmerFinEquiv using (Fin1≃Unit ; LehmerInd)

Lehmer2 = Lehmer

Lehmer1-Lehmer2-equiv : (n : ℕ) →  Lehmer1 n ≃ Lehmer2 (S n)
Lehmer1-Lehmer2-equiv O =
    contr-equiv-Unit (×-level (equiv-preserves-level {A = Unit} {B = Fin 1} (Fin1≃Unit ⁻¹)) ⟨⟩) ⁻¹
                     ∘e contr-equiv-Unit ⟨⟩
Lehmer1-Lehmer2-equiv (S n) =
     Lehmer1 (S n) ≃⟨ (LehmerInd {n}) ⁻¹ ⟩
     Fin (S (S n)) × Lehmer1 n ≃⟨ _ , (×-isemap-r (Fin (S (S n))) (snd (Lehmer1-Lehmer2-equiv n))) ⟩
     Fin (S (S n)) × Lehmer2 (S n) ≃∎