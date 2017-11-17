{-# OPTIONS --without-K --rewriting #-}

module PiFin+.Level1 where

open import PiFin+.Syntax
open import PiFin+.Semantics
open import PiFin+.Level0

open import HoTT

⟦_⟧₀′ : U → N
⟦ T ⟧₀′ = let n = ∣ T ∣ in n , pt (⊙BAut (El n))

⟦_⟧₁′ : {A B : U} → A ⟷ B → ⟦ A ⟧₀′ == ⟦ B ⟧₀′
⟦ unite₊l ⟧₁′ = idp
⟦ swap₊ {A} {B} ⟧₁′ = N-in (+-comm ∣ A ∣ ∣ B ∣)
⟦ assocl₊ {A} {B} {C} ⟧₁′ = N-in (! (+-assoc (∣ A ∣) ∣ B ∣ ∣ C ∣))
⟦ id⟷ ⟧₁′ = idp
⟦ !⟷ p ⟧₁′ = ! ⟦ p ⟧₁′
⟦ p₁ ◎ p₂ ⟧₁′ = ⟦ p₁ ⟧₁′ ∙ ⟦ p₂ ⟧₁′
⟦ p₁ ⊕ p₂ ⟧₁′ = let q₁ = fst= ⟦ p₁ ⟧₁′
                    q₂ = fst= ⟦ p₂ ⟧₁′
                in N-in (ap2 _+_ q₁ q₂)

⟦_⟧₁ : {A B : U} → A ⟷ B → ⟦ A ⟧₀ == ⟦ B ⟧₀
⟦ unite₊l ⟧₁ = idp
⟦ swap₊ {A} {B} ⟧₁ = M₀= (+-comm ∣ A ∣ ∣ B ∣)
⟦ assocl₊ {A} {B} {C} ⟧₁ = M₀= (! (+-assoc (∣ A ∣) ∣ B ∣ ∣ C ∣))
⟦ id⟷ ⟧₁ = idp
⟦ !⟷ p ⟧₁ = ! ⟦ p ⟧₁
⟦ p₁ ◎ p₂ ⟧₁ = ⟦ p₁ ⟧₁ ∙ ⟦ p₂ ⟧₁
⟦ p₁ ⊕ p₂ ⟧₁ = let q₁ = M₀=-out ⟦ p₁ ⟧₁
                   q₂ = M₀=-out ⟦ p₂ ⟧₁
               in M₀= (ap2 _+_ q₁ q₂)

⌜_⌝₁ : {X Y : M} → X == Y → ⌜ X ⌝₀ ⟷ ⌜ Y ⌝₀
⌜ idp ⌝₁ = id⟷

⌜⟦_⟧⌝₁ : {A B : U} → (p : A ⟷ B) → ⌜ ⟦ p ⟧₁ ⌝₁ ⇔ ⌜⟦ A ⟧⌝₀ ◎ p ◎ !⟷ ⌜⟦ B ⟧⌝₀
⌜⟦ unite₊l ⟧⌝₁ = {!!}
⌜⟦ swap₊ ⟧⌝₁ = {!!}
⌜⟦ assocl₊ ⟧⌝₁ = {!!}
⌜⟦ id⟷ ⟧⌝₁ = trans⇔ linv◎r (id⇔ ⊡ idl◎r)
⌜⟦ !⟷ p ⟧⌝₁ = {!!}
⌜⟦ p₁ ◎ p₂ ⟧⌝₁ = {!!}
⌜⟦ p₁ ⊕ p₂ ⟧⌝₁ = {!!}

⟦⌜_⌝⟧₁ : {X Y : M} → (p : X == Y) → ⟦ ⌜ p ⌝₁ ⟧₁ == ap (λ X → ⟦ ⌜ X ⌝₀ ⟧₀) p
⟦⌜ idp ⌝⟧₁ = idp
