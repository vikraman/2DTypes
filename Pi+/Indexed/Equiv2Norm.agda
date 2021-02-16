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

evalNorm₂ : {c₁ c₂ : n ⟷₁^ m} → c₁ ⟷₂^ c₂ → evalNorm₁ c₁ == evalNorm₁ c₂
evalNorm₂ {O} {m} {(c₁ ◎^ c₂ ◎^ c₃)} assoc◎l^ with (⟷₁^-eq-size (c₁ ◎^ c₂ ◎^ c₃))
evalNorm₂ {O} {O} {c₁ ◎^ c₂ ◎^ c₃} assoc◎l^ | idp with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂) | (⟷₁^-eq-size c₃)
... | idp | idp | idp = idp
evalNorm₂ {O} {m} {.((_ ◎^ _) ◎^ _)} (assoc◎r^ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}) with (⟷₁^-eq-size ((c₁ ◎^ c₂) ◎^ c₃))
evalNorm₂ {O} {O} {(_ ◎^ _) ◎^ _} (assoc◎r^ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}) | idp with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂) | (⟷₁^-eq-size c₃)
... | idp | idp | idp = idp
evalNorm₂ {O} {m} {.(id⟷₁^ ◎^ _)} idl◎l^ = {!   !}
evalNorm₂ {O} {m} {c₁} idl◎r^ = {!   !}
evalNorm₂ {O} {m} {.(_ ◎^ id⟷₁^)} idr◎l^ = {!   !}
evalNorm₂ {O} {m} {c₁} idr◎r^ = {!   !}
evalNorm₂ {O} {.0} {.(_ ◎^ !⟷₁^ _)} linv◎l^ = {!   !}
evalNorm₂ {O} {.0} {.id⟷₁^} linv◎r^ = {!   !}
evalNorm₂ {O} {.0} {.(!⟷₁^ _ ◎^ _)} rinv◎l^ = {!   !}
evalNorm₂ {O} {.0} {.id⟷₁^} rinv◎r^ = {!   !}
evalNorm₂ {O} {m} {c₁} id⟷₂^ with (⟷₁^-eq-size c₁)
... | idp = idp
evalNorm₂ {O} {m} {c₁} {c₂} (trans⟷₂^ α α₁) with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂)
... | idp | idp = idp
evalNorm₂ {O} {m} {.(_ ◎^ _)} (α ⊡^ α₁) = {!   !}
evalNorm₂ {S n} {m} {.(_ ◎^ _ ◎^ _)} {.((_ ◎^ _) ◎^ _)} assoc◎l^ = {!   !}
evalNorm₂ {S n} {m} {.((_ ◎^ _) ◎^ _)} {.(_ ◎^ _ ◎^ _)} assoc◎r^ = {!   !}
evalNorm₂ {S n} {m} {.(id⟷₁^ ◎^ c₂)} {c₂} idl◎l^ = {!   !}
evalNorm₂ {S n} {m} {c₁} {.(id⟷₁^ ◎^ c₁)} idl◎r^ = {!   !}
evalNorm₂ {S n} {m} {.(c₂ ◎^ id⟷₁^)} {c₂} idr◎l^ = {!   !}
evalNorm₂ {S n} {m} {c₁} {.(c₁ ◎^ id⟷₁^)} idr◎r^ = {!   !}
evalNorm₂ {S n} {.(S n)} {.(_ ◎^ !⟷₁^ _)} {.id⟷₁^} linv◎l^ = {!   !}
evalNorm₂ {S n} {.(S n)} {.id⟷₁^} {.(_ ◎^ !⟷₁^ _)} linv◎r^ = {!   !}
evalNorm₂ {S n} {.(S n)} {.(!⟷₁^ _ ◎^ _)} {.id⟷₁^} rinv◎l^ = {!   !}
evalNorm₂ {S n} {.(S n)} {.id⟷₁^} {.(!⟷₁^ _ ◎^ _)} rinv◎r^ = {!   !}
evalNorm₂ {S n} {m} {c₁} {.c₁} id⟷₂^ with (⟷₁^-eq-size c₁) 
... | idp = idp
evalNorm₂ {S n} {m} {c₁} {c₂} (trans⟷₂^ α α₁) = {!   !}
evalNorm₂ {S n} {m} {.(_ ◎^ _)} {.(_ ◎^ _)} (α ⊡^ α₁) = {!   !}
evalNorm₂ {S n} {.(S n)} {.(⊕^ id⟷₁^)} {.id⟷₁^} ⊕id⟷₁⟷₂^ = {!   !}
evalNorm₂ {S n} {.(S n)} {.id⟷₁^} {.(⊕^ id⟷₁^)} !⊕id⟷₁⟷₂^ = {!   !}
evalNorm₂ {S n} {.(S _)} {.((⊕^ _) ◎^ ⊕^ _)} {.(⊕^ _ ◎^ _)} hom◎⊕⟷₂^ = {!   !}
evalNorm₂ {S n} {.(S _)} {.(⊕^ _)} {.(⊕^ _)} (resp⊕⟷₂ α) = {!   !}
evalNorm₂ {S n} {.(S _)} {.(⊕^ _ ◎^ _)} {.((⊕^ _) ◎^ ⊕^ _)} hom⊕◎⟷₂^ = {!   !}
evalNorm₂ {S .(S _)} {.(S (S _))} {.((⊕^ ⊕^ _) ◎^ swap₊^)} {.(swap₊^ ◎^ ⊕^ ⊕^ _)} swapr₊⟷₂^ = {!   !}
evalNorm₂ {S .(S _)} {.(S (S _))} {.(swap₊^ ◎^ ⊕^ ⊕^ _)} {.((⊕^ ⊕^ _) ◎^ swap₊^)} swapl₊⟷₂^ = {!   !}

-- evalNorm₂ id⟷₂^ = idp
-- evalNorm₂ (trans⟷₂^ α α₁) = evalNorm₂ α ∙ evalNorm₂ α₁
