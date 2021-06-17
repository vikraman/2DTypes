{-# OPTIONS --without-K --rewriting #-}

module Pi+.Lehmer.Lehmer2 where

open import lib.Base
open import lib.types.Fin
open import lib.types.Sigma
open import HoTT

Lehmer : ℕ → Type₀
Lehmer O = Fin (S O)
Lehmer (S n) = Fin (S (S n)) × Lehmer n

open import Pi+.Lehmer.Lehmer renaming (Lehmer to Lehmer1)
open import Pi+.Lehmer.LehmerLevel
open import Pi+.Lehmer.LehmerFinEquiv using (Fin1≃Unit ; LehmerInd)
open import Pi+.Extra
open import Pi+.Misc

Lehmer2 = Lehmer

Lehmer1-Lehmer2-equiv : {n : ℕ} →  Lehmer1 n ≃ Lehmer2 n
Lehmer1-Lehmer2-equiv {O} = TODO!
Lehmer1-Lehmer2-equiv {S n} =
     Lehmer1 (S n) ≃⟨ (LehmerInd {n}) ⁻¹ ⟩
     Fin (S (S n)) × Lehmer1 n ≃⟨ _ , (×-isemap-r (Fin (S (S n))) (snd (Lehmer1-Lehmer2-equiv {n}))) ⟩
     Fin (S (S n)) × Lehmer2 n ≃∎ 
