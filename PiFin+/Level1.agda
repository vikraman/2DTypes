{-# OPTIONS --without-K #-}

module PiFin+.Level1 where

open import PiFin+.Syntax
open import PiFin+.Semantics
open import PiFin+.Level0

open import HoTT

+-cong : {m n o p : ℕ} → m == o → n == p → m + n == o + p
+-cong idp idp = idp

⟦_⟧₀′ : U → N
⟦ T ⟧₀′ = let n = ∣ T ∣ in n , pt (⊙BAut (El n))

⟦_⟧₁ : {A B : U} → A ⟷ B → ⟦ A ⟧₀′ == ⟦ B ⟧₀′
⟦ unite₊l ⟧₁ = idp
⟦ swap₊ {A} {B} ⟧₁ = pair= (+-comm ∣ A ∣ ∣ B ∣) (N-in (+-comm ∣ A ∣ ∣ B ∣))
⟦ assocl₊ {A} {B} {C} ⟧₁ = pair= (HoTT.! (+-assoc (∣ A ∣) ∣ B ∣ ∣ C ∣)) (N-in (HoTT.! (+-assoc (∣ A ∣) ∣ B ∣ ∣ C ∣)))
⟦ id⟷ ⟧₁ = idp
⟦ _⟷_.! p ⟧₁ = HoTT.! ⟦ p ⟧₁
⟦ p₁ ◎ p₂ ⟧₁ = ⟦ p₁ ⟧₁ ∙ ⟦ p₂ ⟧₁
⟦ p₁ ⊕ p₂ ⟧₁ = let q₁ = fst= ⟦ p₁ ⟧₁
                   q₂ = fst= ⟦ p₂ ⟧₁
               in pair= (+-cong q₁ q₂) (N-in (+-cong q₁ q₂))

⌜_⌝₁ : {X Y : M} → X == Y → ⌜ X ⌝₀ ⟷ ⌜ Y ⌝₀
⌜ idp ⌝₁ = id⟷
