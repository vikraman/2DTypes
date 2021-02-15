{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

module Pi+.Indexed.Equiv2Norm where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.UFin
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
evalNorm₂ {O} α = TODO
evalNorm₂ {S n} assoc◎l^ = TODO
evalNorm₂ {S n} assoc◎r^ = TODO
evalNorm₂ {S n} idl◎l^ = TODO
evalNorm₂ {S n} idl◎r^ = TODO
evalNorm₂ {S n} idr◎l^ = TODO
evalNorm₂ {S n} idr◎r^ = TODO
evalNorm₂ {S n} linv◎l^ = TODO
evalNorm₂ {S n} linv◎r^ = TODO
evalNorm₂ {S n} rinv◎l^ = TODO
evalNorm₂ {S n} rinv◎r^ = TODO
evalNorm₂ {S n} id⟷₂^ = TODO
evalNorm₂ {S n} (trans⟷₂^ α α₁) = TODO
evalNorm₂ {S n} (α ⊡^ α₁) = TODO
evalNorm₂ {S n} ⊕id⟷₁⟷₂^ = TODO
evalNorm₂ {S n} !⊕id⟷₁⟷₂^ = TODO
evalNorm₂ {S n} hom◎⊕⟷₂^ = TODO
evalNorm₂ {S n} (resp⊕⟷₂ α) = TODO
evalNorm₂ {S O} hom⊕◎⟷₂^ = TODO
evalNorm₂ {S (S n)} hom⊕◎⟷₂^ = TODO
evalNorm₂ {S .(S _)} swapr₊⟷₂^ = TODO
evalNorm₂ {S .(S _)} swapl₊⟷₂^ = TODO