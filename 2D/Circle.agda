{-# OPTIONS --without-K --rewriting #-}

module 2D.Circle where

open import Relation.Binary.PropositionalEquality

module _ {a b} {A : Set a} {B : Set b} {x : A} where
  ap : {y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  ap f refl = refl

module _ {a p} {A : Set a} (P : A → Set p) {x : A} where
  transport : {y : A} → x ≡ y → P x → P y
  transport refl p = p

  PathOver : {y : A} → x ≡ y → P x → P y → Set p
  PathOver p u v = transport p u ≡ v

  syntax PathOver P p u v = u ≡ v [ P ↓ p ]

module _ {a b} {A : Set a} {B : A → Set b} {x : A} where
  apd : {y : A} → (f : (x : A) → B x)
      → (p : x ≡ y) → f x ≡ f y [ B ↓ p ]
  apd f refl = refl

{-# BUILTIN REWRITE _≡_ #-}

postulate
  S¹ : Set
  base : S¹
  loop : base ≡ base

module _ {p} (P : Set p) (pbase : P) (ploop : pbase ≡ pbase) where
  postulate
    rec-S¹ : S¹ → P
    βrec-S¹-base : rec-S¹ base ≡ pbase
    {-# REWRITE βrec-S¹-base #-}
    βrec-S¹-loop : ap rec-S¹ loop ≡ ploop

module _ {p} (P : S¹ → Set p) (pbase : P base)
         (ploop : transport P loop pbase ≡ pbase) where
  postulate
    ind-S¹ : (s : S¹) → P s
    βind-S¹-base : ind-S¹ base ≡ pbase
    {-# REWRITE βind-S¹-base #-}
    βind-S¹-loop : apd ind-S¹ loop ≡ ploop
