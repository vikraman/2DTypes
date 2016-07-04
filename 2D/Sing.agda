{-# OPTIONS --without-K #-}

module 2D.Sing where

open import 2D.Types
open import 2D.Power

open import Relation.Binary.PropositionalEquality
open import Data.Integer using (ℤ)

record Sing {τ : U} (p : τ ⟷ τ) : Set where
  constructor ⟪_,_⟫
  field
    p' : τ ⟷ τ
    eq : p' ⇔ p

{- This works, but leads to things that are too complicated,
  so try a forgetful definition first
_∘S_ : {τ : U} {p : τ ⟷ τ} → Sing p → Sing p → Sing p
⟪ p₁ , e₁ ⟫ ∘S ⟪ p₂ , e₂ ⟫ =
  ⟪ ! p₂ ◎ p₁ ◎ p₂ , assoc◎l ● (((⇔! e₂) ⊡ e₁) ⊡ id⇔) ● (rinv◎l ⊡ id⇔) ●
                     idl◎l ● e₂ ⟫
-}
_∘S_ : {τ : U} {p : τ ⟷ τ} → Sing p → Sing p → Sing p
s ∘S _ = s

-- all Sings are the same
sing⇔ : {τ : U} {p : τ ⟷ τ} (q r : Sing p) → Sing.p' q ⇔ Sing.p' r
sing⇔ {_} {_} ⟪ _ , α ⟫ ⟪ _ , β ⟫ = α ● 2! β

-- From a combinator to a Sing
sing : {τ : U} (p : τ ⟷ τ) → Sing p
sing p = ⟪ p , id⇔ ⟫

-- this is a combination of Sing and Iter
record SingI {τ : U} {p : τ ⟷ τ} (q : τ ⟷ τ) : Set where
  constructor si
  field
    i : ℤ
    eq : q ⇔ (p ^ i)
