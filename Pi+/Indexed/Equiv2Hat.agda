{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting --overlapping-instances #-}

module Pi+.Indexed.Equiv2Hat where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.UFin
open import Pi+.Level0
open import Pi+.Extra
open import Pi+.UFin.BAut

open import Pi+.Indexed.Equiv0Hat
open import Pi+.Indexed.Equiv1Hat

open import lib.Basics
open import lib.types.Fin
open import lib.types.List
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct

private
    variable
        n m : ℕ

eval^₂ : {t₁ : U n} {t₂ : U m} {c₁ c₂ : t₁ ⟷₁ t₂} → c₁ ⟷₂ c₂ → eval^₁ c₁ ⟷₂^ eval^₁ c₂
eval^₂ α = {!   !}

quote^₂ : {t₁ : U^ n} {t₂ : U^ m} {c₁ c₂ : t₁ ⟷₁^ t₂} → c₁ ⟷₂^ c₂ → quote^₁ c₁ ⟷₂ quote^₁ c₂
quote^₂ α = {!   !}