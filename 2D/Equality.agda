{-# OPTIONS --without-K #-}

module 2D.Equality where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import 2D.Types
open import 2D.Frac

data [_]_≈_ : (T : U) → V T → V T → Set where
  tt≈ : [ 𝟙 ] (tt , refl) ≈ (tt , refl)
  inj₁≈ : ∀ {T S x y x⇒x y⇒y}
        → [ T ] (x , x⇒x) ≈ (y , y⇒y)
        → [ T ⊕ S ] (inj₁ x , x⇒x) ≈ (inj₁ y , y⇒y)
  inj₂≈ : ∀ {T S x y x⇒x y⇒y}
        → [ S ] (x , x⇒x) ≈ (y , y⇒y)
        → [ T ⊕ S ] (inj₂ x , x⇒x) ≈ (inj₂ y , y⇒y)
  proj≈ : ∀ {T S t₁ t₂ s₁ s₂ t₁⇒t₁ t₂⇒t₂ s₁⇒s₁ s₂⇒s₂}
        → [ T ] (t₁ , t₁⇒t₁) ≈ (t₂ , t₂⇒t₂)
        → [ S ] (s₁ , s₁⇒s₁) ≈ (s₂ , s₂⇒s₂)
        → [ T ⊗ S ] ((t₁ , s₁) , (t₁⇒t₁ , s₁⇒s₁)) ≈ ((t₂ , s₂) , (t₂⇒t₂ , s₂⇒s₂))
  #≈ : ∀ {τ x p α q β} → Perm.p' {τ} p ⇔ Perm.p' {τ} q → [ # x ] (p , α) ≈ (q , β)
  1/#≈ : ∀ {τ x p q} → Perm.p' {τ} p ⇔ Perm.p' {τ} q → [ 1/# x ] (tt , p) ≈ (tt , q)

refl≈[_] : (T : U) → (x : V T) → [ T ] x ≈ x
refl≈[ 𝟘 ] (() , _)
refl≈[ 𝟙 ] (tt , refl) = tt≈
refl≈[ T ⊕ S ] (inj₁ x , x⇒x) = inj₁≈ (refl≈[ T ] (x , x⇒x))
refl≈[ T ⊕ S ] (inj₂ y , y⇒y) = inj₂≈ (refl≈[ S ] (y , y⇒y))
refl≈[ T ⊗ S ] ((x , y) , (x⇒x , y⇒y)) = proj≈ (refl≈[ T ] (x , x⇒x)) (refl≈[ S ] (y , y⇒y))
refl≈[ # x ] (p , α) = #≈ α
refl≈[ 1/# x ] (tt , perm iter p' p'⇔p^i) = 1/#≈ id⇔

sym≈[_] : (T : U) → (x y : V T) → [ T ] x ≈ y → [ T ] y ≈ x
sym≈[ 𝟘 ] (() , _) (() , _)
sym≈[ 𝟙 ] (tt , refl) (tt , refl) tt≈ = tt≈
sym≈[ T ⊕ S ] (inj₁ x , x⇒x) (inj₁ y , y⇒y) (inj₁≈ p) = inj₁≈ (sym≈[ T ] (x , x⇒x) (y , y⇒y) p)
sym≈[ T ⊕ S ] (inj₂ x , x⇒x) (inj₁ y , y⇒y) ()
sym≈[ T ⊕ S ] (inj₁ x , x⇒x) (inj₂ y , y⇒y) ()
sym≈[ T ⊕ S ] (inj₂ x , x⇒x) (inj₂ y , y⇒y) (inj₂≈ p) = inj₂≈ (sym≈[ S ] (x , x⇒x) (y , y⇒y) p)
sym≈[ T ⊗ S ] ((t₁ , s₁) , t₁⇒t₁ , s₁⇒s₁) ((t₂ , s₂) , t₂⇒t₂ , s₂⇒s₂) (proj≈ p₁ p₂) =
  proj≈ (sym≈[ T ] (t₁ , t₁⇒t₁) (t₂ , t₂⇒t₂) p₁) (sym≈[ S ] (s₁ , s₁⇒s₁) (s₂ , s₂⇒s₂) p₂)
sym≈[ # x ] (p , α) (q , β) (#≈ p') = #≈ (2! p')
sym≈[ 1/# x ] (tt , p) (tt , q) (1/#≈ p') = 1/#≈ (2! p')

trans≈[_] : (T : U) → (x y z : V T) → [ T ] x ≈ y → [ T ] y ≈ z → [ T ] x ≈ z
trans≈[ 𝟘 ] (() , _) (() , _) (() , _)
trans≈[ 𝟙 ] (tt , refl) (tt , refl) (tt , refl) tt≈ tt≈ = tt≈
trans≈[ T ⊕ S ] (inj₁ x , x⇒x) (inj₁ y , y⇒y) (inj₁ z , z⇒z) (inj₁≈ p) (inj₁≈ q) =
  inj₁≈ (trans≈[ T ] (x , x⇒x) (y , y⇒y) (z , z⇒z) p q)
trans≈[ T ⊕ S ] (inj₂ x , x⇒x) (inj₁ y , y⇒y) (inj₁ z , z⇒z) () _
trans≈[ T ⊕ S ] (inj₁ x , x⇒x) (inj₂ y , y⇒y) (inj₁ z , z⇒z) () _
trans≈[ T ⊕ S ] (inj₂ x , x⇒x) (inj₂ y , y⇒y) (inj₁ z , z⇒z) _ ()
trans≈[ T ⊕ S ] (inj₁ x , x⇒x) (inj₂ y , y⇒y) (inj₂ z , z⇒z) () _
trans≈[ T ⊕ S ] (inj₂ x , x⇒x) (inj₁ y , y⇒y) (inj₂ z , z⇒z) () _
trans≈[ T ⊕ S ] (inj₂ x , x⇒x) (inj₂ y , y⇒y) (inj₂ z , z⇒z) (inj₂≈ p) (inj₂≈ q) =
  inj₂≈ (trans≈[ S ] (x , x⇒x) (y , y⇒y) (z , z⇒z) p q)
trans≈[ T ⊗ S ] ((t₁ , s₁) , t₁⇒t₁ , s₁⇒s₁) ((t₂ , s₂) , t₂⇒t₂ , s₂⇒s₂) ((t₃ , s₃) , t₃⇒t₃ , s₃⇒s₃) (proj≈ p₁ p₂) (proj≈ q₁ q₂) =
  proj≈ (trans≈[ T ] (t₁ , t₁⇒t₁) (t₂ , t₂⇒t₂) (t₃ , t₃⇒t₃) p₁ q₁)
        (trans≈[ S ] (s₁ , s₁⇒s₁) (s₂ , s₂⇒s₂) (s₃ , s₃⇒s₃) p₂ q₂)
trans≈[ # x ] (p , α) (q , β) (r , γ) (#≈ p₁) (#≈ p₂) = #≈ (trans⇔ p₁ p₂)
trans≈[ 1/# x ] (tt , p) (tt , q) (tt , r) (1/#≈ p₁) (1/#≈ p₂) = 1/#≈ (trans⇔ p₁ p₂)

≡⇒≈[_] : (T : U) → {x y : V T} → x ≡ y → [ T ] x ≈ y
≡⇒≈[ T ] {x} refl = refl≈[ T ] x

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
