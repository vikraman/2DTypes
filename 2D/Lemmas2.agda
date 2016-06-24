{-# OPTIONS --without-K #-}

module 2D.Lemmas2 where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import 2D.Types
open import 2D.Frac
open import 2D.Equality
open import 2D.opsem

𝓐𝓹-id : {T : U} → (v : V T) → [ T ] (𝓐𝓹 (Prim {T} id⟷) v) ≈ v
𝓐𝓹-id v = refl≈[ _ ] v

𝓐𝓹-◎ : {T : U} → (c₁ c₂ : T ⟷ T) → (v : V T) → [ T ] (𝓐𝓹 (c₁ ◎ c₂) v) ≈ (𝓐𝓹 c₂ (𝓐𝓹 c₁ v))
𝓐𝓹-◎ {𝟘} c₁ c₂ (() , _)
𝓐𝓹-◎ {𝟙} (Prim id⟷) (Prim id⟷) (tt , refl) = tt≈
𝓐𝓹-◎ {𝟙} (Prim id⟷) (c₂ ◎ c₃) (tt , refl) = refl≈[ 𝟙 ] (𝓐𝓹 c₃ (𝓐𝓹 c₂ (tt , refl)))
𝓐𝓹-◎ {𝟙} (c₁ ◎ c₂) (Prim id⟷) (tt , refl) = refl≈[ 𝟙 ] (𝓐𝓹 c₂ (𝓐𝓹 c₁ (tt , refl)))
𝓐𝓹-◎ {𝟙} (c₁ ◎ c₂) (c₃ ◎ c₄) (tt , refl) = refl≈[ 𝟙 ] (𝓐𝓹 c₄ (𝓐𝓹 c₃ (𝓐𝓹 c₂ (𝓐𝓹 c₁ (tt , refl)))))
𝓐𝓹-◎ {T ⊕ S} c₁ c₂ (inj₁ x , x⇒x) = refl≈[ T ⊕ S ] (𝓐𝓹 c₂ (𝓐𝓹 c₁ (inj₁ x , x⇒x)))
𝓐𝓹-◎ {T ⊕ S} c₁ c₂ (inj₂ y , y⇒y) = refl≈[ T ⊕ S ] (𝓐𝓹 c₂ (𝓐𝓹 c₁ (inj₂ y , y⇒y)))
𝓐𝓹-◎ {T ⊗ S} c₁ c₂ ((x , y) , (x⇒x , y⇒y)) = refl≈[ T ⊗ S ] (𝓐𝓹 c₂ (𝓐𝓹 c₁ ((x , y) , x⇒x , y⇒y)))
𝓐𝓹-◎ {# x} c₁ c₂ (p , α) = refl≈[ # x ] (𝓐𝓹 c₂ (𝓐𝓹 c₁ (p , α)))
𝓐𝓹-◎ {1/# x} c₁ c₂ (tt , p) = refl≈[ 1/# x ] (𝓐𝓹 c₂ (𝓐𝓹 c₁ (tt , p)))
