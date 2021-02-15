{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting --overlapping-instances #-}

module Pi+.Indexed.Equiv2Norm where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.UFin
open import Pi+.Level0
open import Pi+.Extra
open import Pi+.UFin.BAut

open import Pi+.Indexed.Equiv0Norm
open import Pi+.Indexed.Equiv1Norm

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

evalNorm₂ : {t₁ : U^ n} {t₂ : U^ m} {c₁ c₂ : t₁ ⟷₁^ t₂} → c₁ ⟷₂^ c₂ → evalNorm₁ c₁ == evalNorm₁ c₂
evalNorm₂ {O} α = {!   !}
evalNorm₂ {S n} assoc◎l^ = {!   !}
evalNorm₂ {S n} assoc◎r^ = {!   !}
evalNorm₂ {S n} idl◎l^ = {!   !}
evalNorm₂ {S n} idl◎r^ = {!   !}
evalNorm₂ {S n} idr◎l^ = {!   !}
evalNorm₂ {S n} idr◎r^ = {!   !}
evalNorm₂ {S n} linv◎l^ = {!   !}
evalNorm₂ {S n} linv◎r^ = {!   !}
evalNorm₂ {S n} rinv◎l^ = {!   !}
evalNorm₂ {S n} rinv◎r^ = {!   !}
evalNorm₂ {S n} id⟷₂^ = {!   !}
evalNorm₂ {S n} (trans⟷₂^ α α₁) = {!   !}
evalNorm₂ {S n} (α ⊡^ α₁) = {!   !}
evalNorm₂ {S n} ⊕id⟷₁⟷₂^ = {!   !}
evalNorm₂ {S n} !⊕id⟷₁⟷₂^ = {!   !}
evalNorm₂ {S n} hom◎⊕⟷₂^ = {!   !}
evalNorm₂ {S n} (resp⊕⟷₂ α) = {!   !}
evalNorm₂ {S O} hom⊕◎⟷₂^ = {!   !}
evalNorm₂ {S (S n)} hom⊕◎⟷₂^ = {!   !}
evalNorm₂ {S .(S _)} swapr₊⟷₂^ = {!   !}
evalNorm₂ {S .(S _)} swapl₊⟷₂^ = {!   !}