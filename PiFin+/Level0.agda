{-# OPTIONS --without-K --rewriting #-}

module PiFin+.Level0 where

open import PiFin+.Syntax
open import PiFin+.Semantics

open import HoTT

∣_∣ : U → ℕ
∣ ZERO ∣ = O
∣ ONE ∣ = S O
∣ PLUS A B ∣ = ∣ A ∣ + ∣ B ∣

⟦_⟧₀ : U → M
⟦ T ⟧₀ = let n = ∣ T ∣ in  M₀ n
-- pt (⊙BAut (El n))

⟪_⟫ : ℕ → U
⟪ O ⟫ = ZERO
⟪ S n ⟫ = PLUS ONE ⟪ n ⟫

⌜_⌝₀ : M → U
⌜ T , n , φ ⌝₀ = ⟪ n ⟫

∣⟪_⟫∣ : (n : ℕ) → ∣ ⟪ n ⟫ ∣ == n
∣⟪ O ⟫∣ = idp
∣⟪ S n ⟫∣ = ap S ∣⟪ n ⟫∣

⟦⌜_⌝⟧₀ : (T : M) → Trunc -1 (⟦ ⌜ T ⌝₀ ⟧₀ == T)
⟦⌜ T@(X , n , φ) ⌝⟧₀ = Trunc-elim {P = λ _ → Trunc -1 (⟦ ⌜ T ⌝₀ ⟧₀ == T)} ([_] ∘ f) φ
  where f : El n == X → ⟦ ⌜ T ⌝₀ ⟧₀ == T
        f idp = is-equiv.g finite-types-is-univ (transport-equiv (idf Type₀) (ap El ∣⟪ n ⟫∣))

canonU : U → U
canonU T = ⟪ ∣ T ∣ ⟫

⟪+⟫ : (m n : ℕ) → PLUS ⟪ m ⟫ ⟪ n ⟫ ⟷ ⟪ m + n ⟫
⟪+⟫ O n = unite₊l
⟪+⟫ (S m) n = assocr₊ ◎ (id⟷ ⊕ ⟪+⟫ m n)

normC : (t : U) → t ⟷ canonU t
normC ZERO = id⟷
normC ONE  = uniti₊l ◎ swap₊
normC (PLUS A B) = (normC A ⊕ normC B) ◎ ⟪+⟫ ∣ A ∣ ∣ B ∣

⌜⟦_⟧⌝₀ : (T : U) → ⌜ ⟦ T ⟧₀ ⌝₀ ⟷ T
⌜⟦ ZERO ⟧⌝₀ = id⟷
⌜⟦ ONE ⟧⌝₀ = swap₊ ◎ unite₊l
⌜⟦ PLUS T₁ T₂ ⟧⌝₀ = _⟷_.! (normC (PLUS T₁ T₂))
