{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Level0 where

open import lib.Base
open import lib.types.Nat renaming (_+_ to _+ℕ_)

open import Pi+.Syntax as Pi

ℕ→Pi : ℕ → U
ℕ→Pi O = O
ℕ→Pi (S x) = I + (ℕ→Pi x)

⟪_⟫ : ℕ → U
⟪ O ⟫ = O
⟪ S n ⟫ = I + ⟪ n ⟫

∣_∣ : U → ℕ
∣ O ∣ = 0
∣ I ∣ = 1
∣ X + Y ∣ = ∣ X ∣ +ℕ ∣ Y ∣

∣⟪_⟫∣ : (n : ℕ) → ∣ ⟪ n ⟫ ∣ == n
∣⟪ O ⟫∣ = idp
∣⟪ S n ⟫∣ = ap S ∣⟪ n ⟫∣

canonU : U → U
canonU T = ⟪ ∣ T ∣ ⟫

⟪+⟫ : (m n : ℕ) → ⟪ m ⟫ + ⟪ n ⟫ ⟷₁ ⟪ m +ℕ n ⟫
⟪+⟫ O n = unite₊l
⟪+⟫ (S m) n = assocr₊ ◎ (id⟷₁ ⊕ ⟪+⟫ m n)

normC : (t : U) → t ⟷₁ canonU t
normC O = id⟷₁
normC I  = uniti₊l ◎ swap₊
normC (X + Y) = (normC X ⊕ normC Y) ◎ ⟪+⟫ ∣ X ∣ ∣ Y ∣
