{-# OPTIONS --type-in-type --rewriting --without-K #-}

module Univ.Interval where

open import Data.Product
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_)

{-# BUILTIN REWRITE _==_ #-}

module _ {a b} {A : Set a} { B : Set b} {x : A} where

  ap : {y : A} → (f : A → B) → x == y → f x == f y
  ap f refl = refl

module _ {a p} {A : Set a} (P : A → Set p) {x : A} where

  transport : {y : A} → x == y → P x → P y
  transport refl p = p

  PathOver : {y : A} → x == y → P x → P y → Set p
  PathOver p u v = transport p u == v

  syntax PathOver P p u v = u == v [ P ↓ p ]

module _ {a b} {A : Set a} {B : A → Set b} {x : A} where

  apd : {y : A} → (f : (x : A) → B x)
      → (p : x == y) → f x == f y [ B ↓ p ]
  apd f refl = refl

postulate
  I : Set
  ₀ ₁ : I
  𝑢 : ₀ == ₁

module _ {p} (P : Set p) (p₀ p₁ : P) (p𝑢 : p₀ == p₁) where
  postulate
    rec-I : (i : I) → P
    βrec-I₀ : rec-I ₀ == p₀
    βrec-I₁ : rec-I ₁ == p₁
    {-# REWRITE βrec-I₀ #-}
    {-# REWRITE βrec-I₁ #-}
    βrec-I𝑢 : ap rec-I 𝑢 == p𝑢
    {-# REWRITE βrec-I𝑢 #-}

module _ {p} (P : I → Set p)
         (p₀ : P ₀) (p₁ : P ₁)
         (p𝑢 : p₀ == p₁ [ P ↓ 𝑢 ]) where
  postulate
    ind-I : (i : I) → P i
    βind-I₀ : ind-I ₀ == p₀
    βind-I₁ : ind-I ₁ == p₁
    {-# REWRITE βind-I₀ #-}
    {-# REWRITE βind-I₁ #-}
    βind-I𝑢 : apd ind-I 𝑢 == p𝑢
    {-# REWRITE βind-I𝑢 #-}

module _ {a b} {A : Set a} {B : Set b} (f g : A → B) (p : ∀ x → f x == g x) where

  α : A → I → B
  α a = rec-I B (f a) (g a) (p a)

  β : I → A → B
  β i a = α a i

  funext : f == g
  funext = ap β 𝑢

open import Univ.Universe

module _ (Univ : Universe) where
  open Univ.Universe.Universe Univ

  Equiv : (A B : U) → Set
  Equiv A B = Σ[ P ∈ (I → Set) ] ((P ₀ == El A) × (P ₁ == El B))

  syntax Equiv A B = A ≃ B
