{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi.Equiv.Equiv0Hat where

open import Pi.Syntax.Pi+.Indexed as Pi
open import Pi.Syntax.Pi^ as Pi^
open import Pi.UFin.UFin
open import Pi.Extra

open import lib.Basics
open import lib.types.Fin
open import lib.types.List hiding (_++_)
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct
open import lib.types.Nat as N renaming (_+_ to _++_)

private
  variable
    n m o p : ℕ

quote^₀ : (n : ℕ) → U n
quote^₀ O = O
quote^₀ (S n) = I U.+ quote^₀ n

quote^₀++ : (n m : ℕ) → quote^₀ (n ++ m) ⟷₁ quote^₀ n U.+ quote^₀ m
quote^₀++ O m = uniti₊l
quote^₀++ (S n) m = (id⟷₁ ⊕ quote^₀++ n m) ◎ assocl₊

eval^₀ : U n → ℕ
eval^₀ {n} t = n

quote-eval^₀ : (t : U n) → quote^₀ (eval^₀ t) ⟷₁ t
quote-eval^₀ O = id⟷₁
quote-eval^₀ I = unite₊r
quote-eval^₀ (t₁ U.+ t₂) = quote^₀++ (eval^₀ t₁) (eval^₀ t₂) ◎ (quote-eval^₀ t₁ ⊕ quote-eval^₀ t₂)

eval-quote^==₀ : (n : ℕ) → eval^₀ (quote^₀ n) == n
eval-quote^==₀ n = idp

eval-quote^₀ : (n : ℕ) → eval^₀ (quote^₀ n) ⟷₁^ n
eval-quote^₀ n = id⟷₁^
