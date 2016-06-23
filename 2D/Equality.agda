{-# OPTIONS --without-K #-}

module 2D.Equality where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Categories.Category
open import 2D.Types
open import 2D.Frac

V : (T : U) → Set
V T = let ℂ , _ = ⟦ T ⟧
          open Category ℂ
      in Σ[ v ∈ Obj ] (v ⇒ v)

open import Relation.Binary.PropositionalEquality

[_]_≈_ : (T : U) → V T → V T → Set
[ 𝟘 ] () , _ ≈ _
[ 𝟙 ] (tt , refl) ≈ (tt , refl) = ⊤
[ T ⊕ S ] (inj₁ x , x⇒x) ≈ (inj₁ y , y⇒y) = [ T ] (x , x⇒x) ≈ (y , y⇒y)
[ T ⊕ S ] (inj₂ x , x⇒x) ≈ (inj₁ y , y⇒y) = ⊥
[ T ⊕ S ] (inj₁ x , x⇒x) ≈ (inj₂ y , y⇒y) = ⊥
[ T ⊕ S ] (inj₂ x , x⇒x) ≈ (inj₂ y , y⇒y) = [ S ] (x , x⇒x) ≈ (y , y⇒y)
[ T ⊗ S ] ((t₁ , s₁) , (t₁⇒t₁ , s₁⇒s₁)) ≈ ((t₂ , s₂) , (t₂⇒t₂ , s₂⇒s₂)) =
  ([ T ] (t₁ , t₁⇒t₁) ≈ (t₂ , t₂⇒t₂)) × ([ S ] (s₁ , s₁⇒s₁) ≈ (s₂ , s₂⇒s₂))
[ # x ] (p , α) ≈ (q , β) = Perm.p' p ⇔ Perm.p' q
[ 1/# x ] (tt , p) ≈ (tt , q) = Perm.p' p ⇔ Perm.p' q

refl≈[_] : (T : U) → (x : V T) → [ T ] x ≈ x
refl≈[ 𝟘 ] (() , _)
refl≈[ 𝟙 ] (tt , refl) = tt
refl≈[ T ⊕ S ] (inj₁ x , x⇒x) = refl≈[ T ] (x , x⇒x)
refl≈[ T ⊕ S ] (inj₂ y , y⇒y) = refl≈[ S ] (y , y⇒y)
refl≈[ T ⊗ S ] ((x , y) , (x⇒x , y⇒y)) = refl≈[ T ] (x , x⇒x) , refl≈[ S ] (y , y⇒y)
refl≈[ # x ] (p , α) = α
refl≈[ 1/# x ] (tt , perm iter p' p'⇔p^i) = id⇔

sym≈[_] : (T : U) → (x y : V T) → [ T ] x ≈ y → [ T ] y ≈ x
sym≈[ 𝟘 ] (() , _) (() , _)
sym≈[ 𝟙 ] (tt , refl) (tt , refl) tt = tt
sym≈[ T ⊕ S ] (inj₁ x , x⇒x) (inj₁ y , y⇒y) p = {!!} -- groupoid
sym≈[ T ⊕ S ] (inj₂ x , x⇒x) (inj₁ y , y⇒y) = {!!}
sym≈[ T ⊕ S ] (inj₁ x , x⇒x) (inj₂ y , y⇒y) = {!!}
sym≈[ T ⊕ S ] (inj₂ x , x⇒x) (inj₂ y , y⇒y) = {!!}
sym≈[ T ⊗ S ] ((t₁ , s₁) , (t₁⇒t₁ , s₁⇒s₁)) ((t₂ , s₂) , (t₂⇒t₂ , s₂⇒s₂)) = {!!}
sym≈[ # x ] (p , α) (q , β) p' = 2! p'
sym≈[ 1/# x ] (tt , p) (tt , q) p' = 2! p'

trans≈[_] : (T : U) → (x y z : V T) → [ T ] x ≈ y → [ T ] y ≈ z → [ T ] x ≈ z
trans≈[ 𝟘 ] (() , _) (() , _) (() , _)
trans≈[ 𝟙 ] (tt , refl) (tt , refl) (tt , refl) tt tt = tt
trans≈[ T ⊕ S ] (inj₁ x , x⇒x) (inj₁ y , y⇒y) (inj₁ z , z⇒z) p q = {!!}
trans≈[ T ⊕ S ] (inj₂ x , x⇒x) (inj₁ y , y⇒y) (inj₁ z , z⇒z) p q = {!!}
trans≈[ T ⊕ S ] (inj₁ x , x⇒x) (inj₂ y , y⇒y) (inj₁ z , z⇒z) p q = {!!}
trans≈[ T ⊕ S ] (inj₁ x , x⇒x) (inj₁ y , y⇒y) (inj₂ z , z⇒z) p q = {!!}
trans≈[ T ⊕ S ] (inj₂ x , x⇒x) (inj₂ y , y⇒y) (inj₁ z , z⇒z) p q = {!!}
trans≈[ T ⊕ S ] (inj₁ x , x⇒x) (inj₂ y , y⇒y) (inj₂ z , z⇒z) p q = {!!}
trans≈[ T ⊕ S ] (inj₂ x , x⇒x) (inj₁ y , y⇒y) (inj₂ z , z⇒z) p q = {!!}
trans≈[ T ⊕ S ] (inj₂ x , x⇒x) (inj₂ y , y⇒y) (inj₂ z , z⇒z) p q = {!!}
trans≈[ T ⊗ S ] ((t₁ , s₁) , (t₁⇒t₁ , s₁⇒s₁)) ((t₂ , s₂) , (t₂⇒t₂ , s₂⇒s₂)) ((t₃ , s₃) , (t₃⇒t₃ , s₃⇒s₃)) = {!!}
trans≈[ # x ] (p , α) (q , β) (r , γ) p' q' = trans⇔ p' q'
trans≈[ 1/# x ] (tt , p) (tt , q) (tt , r) p' q' = trans⇔ p' q'

open import Relation.Binary

≈-isEquivalence[_] : (T : U) → IsEquivalence [ T ]_≈_
≈-isEquivalence[ T ] = record { refl = refl≈[ T ] _
                              ; sym = sym≈[ T ] _ _
                              ; trans = trans≈[ T ] _ _ _
                              }

≈-setoid[_] : (T : U) → Setoid _ _
≈-setoid[ T ] = record { Carrier = V T
                       ; _≈_ = [ T ]_≈_
                       ; isEquivalence = ≈-isEquivalence[ T ]
                       }

module EqR (T : U) where
  open import Relation.Binary.EqReasoning ≈-setoid[ T ] public
