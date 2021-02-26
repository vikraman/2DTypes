{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

module Pi+.Indexed.Equiv2Hat where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.UFin
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
open import lib.types.Nat as N

private
    variable
        n m : ℕ

eval^₂ : {t₁ : U n} {t₂ : U m} {c₁ c₂ : t₁ ⟷₁ t₂} → c₁ ⟷₂ c₂ → eval^₁ c₁ ⟷₂^ eval^₁ c₂
eval^₂ assoc◎l = assoc◎l^
eval^₂ assoc◎r = assoc◎r^
eval^₂ (assocl₊l {n₁} {_} {n₂} {_} {n₃} {_} {n₄} {_} {n₅} {_} {n₆} {_}) with (N.+-assoc n₂ n₄ n₆) | (N.+-assoc n₁ n₃ n₅)
... | p | q = TODO
eval^₂ assocl₊r = TODO
eval^₂ assocr₊r = TODO
eval^₂ assocr₊l = TODO
eval^₂ idl◎l = idl◎l^
eval^₂ idl◎r = idl◎r^
eval^₂ idr◎l = idr◎l^
eval^₂ idr◎r = idr◎r^
eval^₂ linv◎l = TODO
eval^₂ linv◎r = TODO
eval^₂ rinv◎l = TODO
eval^₂ rinv◎r = TODO
eval^₂ unite₊l⟷₂l = TODO
eval^₂ unite₊l⟷₂r = TODO
eval^₂ uniti₊l⟷₂l = TODO
eval^₂ uniti₊l⟷₂r = TODO
eval^₂ swapl₊⟷₂ = TODO
eval^₂ swapr₊⟷₂ = TODO
eval^₂ id⟷₂ = id⟷₂^
eval^₂ (trans⟷₂ α₁ α₂) = trans⟷₂^ (eval^₂ α₁) (eval^₂ α₂)
eval^₂ (α₁ ⊡ α₂) = eval^₂ α₁ ⊡^ eval^₂ α₂
eval^₂ (resp⊕⟷₂ α₁ α₂) = TODO
eval^₂ id⟷₁⊕id⟷₁⟷₂ = TODO
eval^₂ split⊕-id⟷₁ = TODO
eval^₂ hom⊕◎⟷₂ = TODO
eval^₂ hom◎⊕⟷₂ = TODO
eval^₂ triangle₊l = TODO
eval^₂ triangle₊r = TODO
eval^₂ pentagon₊l = TODO
eval^₂ pentagon₊r = TODO
eval^₂ unite₊l-coh-l = TODO
eval^₂ unite₊l-coh-r = TODO
eval^₂ hexagonr₊l = TODO
eval^₂ hexagonr₊r = TODO
eval^₂ hexagonl₊l = TODO
eval^₂ hexagonl₊r = TODO

!-quote^₁ : (c : n ⟷₁^ m) → quote^₁ (!⟷₁^ c) ⟷₂ !⟷₁ (quote^₁ c)
!-quote^₁ swap₊^ = assoc◎l
!-quote^₁ id⟷₁^ = id⟷₂
!-quote^₁ (c ◎^ c₁) = (!-quote^₁ c₁) ⊡ (!-quote^₁ c)
!-quote^₁ (⊕^ c) = resp⊕⟷₂ id⟷₂ (!-quote^₁ c)

quote^₂ : {c₁ c₂ : n ⟷₁^ m} → c₁ ⟷₂^ c₂ → quote^₁ c₁ ⟷₂ quote^₁ c₂
quote^₂ assoc◎l^ = assoc◎l
quote^₂ assoc◎r^ = assoc◎r
quote^₂ idl◎l^ = idl◎l
quote^₂ idl◎r^ = idl◎r
quote^₂ idr◎l^ = idr◎l
quote^₂ idr◎r^ = idr◎r
quote^₂ linv◎l^ = trans⟷₂ (id⟷₂ ⊡ (!-quote^₁ _)) linv◎l
quote^₂ linv◎r^ = !⟷₂ (trans⟷₂ (id⟷₂ ⊡ (!-quote^₁ _)) linv◎l)
quote^₂ rinv◎l^ = trans⟷₂ ( (!-quote^₁ _) ⊡ id⟷₂) rinv◎l
quote^₂ rinv◎r^ = !⟷₂ (trans⟷₂ ( (!-quote^₁ _) ⊡ id⟷₂) rinv◎l)
quote^₂ id⟷₂^ = id⟷₂
quote^₂ (trans⟷₂^ α α₁) = trans⟷₂ (quote^₂ α) (quote^₂ α₁)
quote^₂ (α ⊡^ α₁) = quote^₂ α ⊡ quote^₂ α₁
quote^₂ ⊕id⟷₁⟷₂^ = id⟷₁⊕id⟷₁⟷₂
quote^₂ !⊕id⟷₁⟷₂^ = split⊕-id⟷₁
quote^₂ hom◎⊕⟷₂^ = trans⟷₂ hom◎⊕⟷₂ (resp⊕⟷₂ idl◎l id⟷₂)
quote^₂ (resp⊕⟷₂ α) = resp⊕⟷₂ id⟷₂ (quote^₂ α)
quote^₂ hom⊕◎⟷₂^ = !⟷₂ (trans⟷₂ hom◎⊕⟷₂ (resp⊕⟷₂ idl◎l id⟷₂))
quote^₂ swapr₊⟷₂^ = TODO
quote^₂ swapl₊⟷₂^ = TODO