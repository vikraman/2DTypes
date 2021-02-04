{-# OPTIONS --rewriting --without-K #-}

module Pi+.LehmerFin.LehmerFinEquiv where

open import HoTT

open import Pi+.Extra
open import Pi+.LehmerFin.FinHelpers

infixr 4 _∷_
data LehmerCode : (n : ℕ) → Type₀ where
  [] : LehmerCode O
  _∷_ : ∀ {n} → Fin (S n) → LehmerCode n → LehmerCode (S n)

isContrLehmerZero : is-contr (LehmerCode 0)
isContrLehmerZero = has-level-in ([] , (λ {[] → idp}))

lehmerSucEquiv : {n : ℕ} -> Fin (S n) × LehmerCode n ≃ LehmerCode (S n)
lehmerSucEquiv = equiv (λ (e , c) → e ∷ c)
                                 (λ { (e ∷ c) → (e , c) })
                                 (λ { (e ∷ c) → idp })
                                 (λ (e , c) → idp)

lehmerEquiv : {n : ℕ} -> (Fin n ≃ Fin n) ≃ LehmerCode n
lehmerEquiv {O} = {!   !}
lehmerEquiv {S n} =
  (Fin (S n) ≃ Fin (S n))                              ≃⟨ i ⟩
  (Σ[ k ∈ Fin (S n) ] (FinExcept fzero ≃ FinExcept k)) ≃⟨ Σ-cong-equiv-snd ii ⟩ -- Σ-isemap-r (_ , ii) ⟩
  (Fin (S n) × (Fin n ≃ Fin n))                        ≃⟨ Σ-cong-equiv-snd (λ _ → lehmerEquiv) ⟩ -- Σ-isemap-r (_ , (λ _ → lehmerEquiv)) ⟩
  (Fin (S n) × LehmerCode n)                           ≃⟨ lehmerSucEquiv ⟩
  LehmerCode (S n) ≃∎