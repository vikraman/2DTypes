{-# OPTIONS --without-K --exact-split --rewriting --allow-unsolved-metas #-}

open import lib.Base
open import lib.NType
import lib.types.Nat as N

module Pi+.Indexed.SyntaxNorm where

private
    variable
      m n o p q r : ℕ

-- Types

data U^ : ℕ → Type₀ where
  O : U^ 0
  I+_ : U^ n → U^ (S n)

private
    variable
      t t₁ t₂ t₃ t₄ t₅ t₆ : U^ n

infixr 40 I+_
infix 30 _⟷₁^_
infixr 50 _◎^_ ⊕^_

-- 1-combinators

data _⟷₁^_  : U^ m → U^ n → Type₀ where
  swap₊^   : I+ (I+ t) ⟷₁^ I+ (I+ t)
  id⟷₁^    : t ⟷₁^ t
  _◎^_     : (t₁ ⟷₁^ t₂) → (t₂ ⟷₁^ t₃) → (t₁ ⟷₁^ t₃)
  ⊕^_      : (t₁ ⟷₁^ t₂) → (I+ t₁ ⟷₁^ I+ t₂)

!⟷₁^ : t₁ ⟷₁^ t₂ → t₂ ⟷₁^ t₁
!⟷₁^ swap₊^ = swap₊^
!⟷₁^ id⟷₁^ = id⟷₁^
!⟷₁^ (c₁ ◎^ c₂) = !⟷₁^ c₂ ◎^ !⟷₁^ c₁
!⟷₁^ (⊕^ c₁) = ⊕^ (!⟷₁^ c₁)
