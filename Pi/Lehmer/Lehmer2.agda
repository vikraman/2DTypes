{-# OPTIONS --without-K --rewriting #-}

module Pi.Lehmer.Lehmer2 where

open import HoTT

Lehmer : ℕ → Type₀
Lehmer O = Fin (S O)
Lehmer (S n) = Fin (S (S n)) × Lehmer n

open import Pi.Lehmer.Lehmer renaming (Lehmer to Lehmer1)
open import Pi.Lehmer.LehmerFinEquiv
  using (LehmerInd)
  renaming (Lehmer-O-level to Lehmer1-O-level)
open import Pi.Extra
open import Pi.Misc

Lehmer2 = Lehmer

instance
  Lehmer-O-level : is-contr (Lehmer O)
  Lehmer-O-level =
    has-level-in ((0 , ltS) , λ { (O , ϕ) → fin= idp ; (S n , ltSR ()) })

  Lehmer-level : {n : ℕ} → is-set (Lehmer n)
  Lehmer-level {O} = contr-is-set Lehmer-O-level
  Lehmer-level {S n} = ×-level Fin-is-set (Lehmer-level {n})

Lehmer1-Lehmer2-equiv : {n : ℕ} →  Lehmer1 n ≃ Lehmer2 n
Lehmer1-Lehmer2-equiv {O} =
  Lehmer1 O ≃⟨ contr-equiv-Unit Lehmer1-O-level ⟩
  Unit ≃⟨ contr-equiv-Unit Lehmer-O-level ⁻¹ ⟩
  Lehmer2 O ≃∎
Lehmer1-Lehmer2-equiv {S n} =
  Lehmer1 (S n) ≃⟨ (LehmerInd {n}) ⁻¹ ⟩
  Fin (S (S n)) × Lehmer1 n ≃⟨ _ , (×-isemap-r (Fin (S (S n))) (snd (Lehmer1-Lehmer2-equiv {n}))) ⟩
  Fin (S (S n)) × Lehmer2 n ≃∎
