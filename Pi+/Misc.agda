{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.Misc where

open import lib.Base
open import lib.Equivalence
open import lib.PathGroupoid

transport2 : ∀ {i j k} {A : Type i} {B : Type j} (C : A → B → Type k) {x1 x2 : A} {y1 y2 : B} (p : x1 == x2) (q : y1 == y2) → (C x1 y1 → C x2 y2)
transport2 C {x1} {x2} {y1} {y2} p q t = t''
    where
        t' : C x1 y2
        t' = transport (C x1) q t

        t'' : C x2 y2
        t'' = transport (λ x -> C x y2) p t'

ap2 : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A → B → C) {x1 x2 : A} {y1 y2 : B}
  → (x1 == x2) → (y1 == y2) → (f x1 y1 == f x2 y2)
ap2 f idp idp = idp

transport2-equiv : ∀ {i j k} {A : Type i} {B : Type j} (C : A → B → Type k) {x1 x2 : A} {y1 y2 : B} (p : x1 == x2) (q : y1 == y2) → (C x1 y1 ≃ C x2 y2)
transport2-equiv C idp idp = ide _

infix  1 begin_

begin_ : {A : Type₀} -> {x y : A} → x == y → x == y
begin_ p = p

cong : {A B : Type₀} -> ∀ (f : A → B) {x y} → x == y → f x == f y
cong f p = ap f p

≡-sym : {A : Type₀} -> {p q : A} -> p == q -> q == p
≡-sym = !

≡-trans : {A : Type₀} -> {p q r : A} -> p == q -> q == r -> p == r
≡-trans = _∙_

idpp : {A : Type₀} -> {x : A} -> x == x
idpp {A} {x} = idp

data _⊎_ (A B : Type₀) : Type₀ where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

data BoolDec (A : Type₀) : Type₀ where
  yes : A -> BoolDec A
  no  : ¬ A -> BoolDec A

data Singleton {i} {A : Type i} (x : A) : Type i where
  _with==_ : (y : A) → x == y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with== idp

Aut : ∀ {ℓ} → Type ℓ → Type ℓ
Aut T = T ≃ T

Ω : ∀ {ℓ} → Σ (Type ℓ) (λ X → X) → Type ℓ
Ω (X , x) = (x == x)