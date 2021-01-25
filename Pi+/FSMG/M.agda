{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.FSMG.M where

open import lib.Base
open import lib.NType
open import lib.PathOver
open import lib.PathGroupoid

open import Pi+.FSMG.Paths
open import Pi+.Extra

module _ {i} where
  postulate
    M : (A : Type i) → Type i

  module _ {A : Type i} where
    infixr 40 _::_
    postulate
      nil : M A
      _::_ : A → M A → M A

      swap : (x y : A) (xs : M A) → x :: y :: xs == y :: x :: xs

      ⬡ : (x y z : A) (xs : M A)
        → swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs) ∙ swap y z (x :: xs)
        == ap (x ::_) (swap y z xs) ∙ swap x z (y :: xs) ∙ ap (z ::_) (swap x y xs)

      swap² : (x y : A) (xs : M A) → swap x y xs ∙ swap y x xs == idp

      instance trunc : has-level 1 (M A)

    module MElim {j} {P : M A → Type j}
      (nil* : P nil)
      (_::*_ : (x : A) {xs : M A} → (xs* : P xs) → P (x :: xs))
      (swap* : (x y : A) {xs : M A} (xs* : P xs)
             → (x ::* (y ::* xs*)) == (y ::* (x ::* xs*)) [ P ↓ swap x y xs ])
      (swap²* : (x y z : A) {xs : M A} (xs* : P xs)
              → (swap* x y xs* ∙ᵈ swap* y x xs*) == idp [ (λ p → (x ::* (y ::* xs*)) == (x ::* (y ::* xs*)) [ P ↓ p ]) ↓ swap² x y xs ])
      (⬡* : (x y z : A) {xs : M A} (xs* : P xs)
          → let p1 = swap* x y (z ::* xs*) ∙ᵈ ($ (y ::*_) (swap* x z xs*) ∙ᵈ swap* y z (x ::* xs*)) in
            let p2 = ($ (x ::*_) (swap* y z xs*) ∙ᵈ (swap* x z (y ::* xs*) ∙ᵈ $ (z ::*_) (swap* x y xs*))) in
            p1 == p2 [ (λ p → (x ::* (y ::* (z ::* xs*))) == (z ::* (y ::* (x ::* xs*))) [ P ↓ p ]) ↓ ⬡ x y z xs ])
      (trunc* : {xs : M A} → has-level 1 (P xs))
      where

      postulate
        f : (xs : M A) → P xs
        f-nil-β : f nil ↦ nil*
        {-# REWRITE f-nil-β #-}
        f-::-β : {x : A} {xs : M A} → f (x :: xs) ↦ (x ::* f xs)
        {-# REWRITE f-::-β #-}

      postulate
        f-swap-β : {x y : A} {xs : M A} → apd f (swap x y xs) == swap* x y (f xs)

    module MRec {j} {P : Type j}
      (nil* : P)
      (_::*_ : (x : A) → P → P)
      (swap* : (x y : A) (xs* : P)
             → (x ::* (y ::* xs*)) == (y ::* (x ::* xs*)))
      (swap²* : (x y z : A) (xs* : P)
              → (swap* x y xs* ∙ swap* y x xs*) == idp)
      (⬡* : (x y z : A) (xs* : P)
          → let p1 = swap* x y (z ::* xs*) ∙ (ap (y ::*_) (swap* x z xs*) ∙ swap* y z (x ::* xs*)) in
            let p2 = (ap (x ::*_) (swap* y z xs*) ∙ (swap* x z (y ::* xs*) ∙ ap (z ::*_) (swap* x y xs*))) in
            p1 == p2)
      (trunc* : has-level 1 P)
      where

      f : M A → P
      f = MElim.f {P = λ _ → P} nil* (λ x p → x ::* p) (λ x y {xs} xs* → ↓-cst-in (swap* x y xs*)) TODO TODO trunc*
