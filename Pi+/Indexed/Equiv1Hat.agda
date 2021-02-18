{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.Indexed.Equiv1Hat where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.UFin
open import Pi+.Extra

open import Pi+.Indexed.Equiv0Hat

open import lib.Basics
open import lib.types.Fin
open import lib.types.List
open import lib.types.BAut
open import lib.types.Nat as N
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct
open import lib.types.Sigma


private
    variable
        n m : ℕ    

quote^₁ : (n ⟷₁^ m) → (quote^₀ n ⟷₁ quote^₀ m)
quote^₁ swap₊^ = assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊
quote^₁ id⟷₁^ = id⟷₁
quote^₁ (c₁ ◎^ c₂) = quote^₁ c₁ ◎ quote^₁ c₂
quote^₁ (⊕^ c₁) = id⟷₁ ⊕ quote^₁ c₁

denorm : {t₁ : U n} {t₂ : U m} → (c : t₁ ⟷₁ t₂) → quote^₀ (eval^₀ t₁) ⟷₁ quote^₀ (eval^₀ t₂)
denorm {t₁ = t₁} {t₂ = t₂} c = (quote-eval^₀ t₁ ◎ c ◎ !⟷₁ (quote-eval^₀ t₂))

denorm← : {t₁ : U n} {t₂ : U m} → (c : quote^₀ (eval^₀ t₁) ⟷₁ quote^₀ (eval^₀ t₂)) → t₁ ⟷₁ t₂
denorm← {t₁ = t₁} {t₂ = t₂} c = (!⟷₁ (quote-eval^₀ t₁)) ◎ c ◎ (quote-eval^₀ t₂)

eval^₁ : {t₁ : U n} {t₂ : U m} → (t₁ ⟷₁ t₂) → (eval^₀ t₁ ⟷₁^ eval^₀ t₂)
eval^₁ unite₊l = id⟷₁^
eval^₁ uniti₊l = id⟷₁^
eval^₁ (swap₊ {t₁ = t₁} {t₂ = t₂}) = ++^-swap (eval^₀ t₁) (eval^₀ t₂)
eval^₁ (assocl₊ {n} {t₁ = t₁} {m} {t₂ = t₂} {o} {t₃ = t₃}) = ++^-id (! (+-assoc n m o))
eval^₁ (assocr₊ {n} {t₁ = t₁} {m} {t₂ = t₂} {o} {t₃ = t₃}) = ++^-id (+-assoc n m o)
eval^₁ id⟷₁ = id⟷₁^
eval^₁ (c₁ ◎ c₂) = eval^₁ c₁ ◎^ eval^₁ c₂
eval^₁ (c₁ ⊕ c₂) = ++^-⊕ (eval^₁ c₁) (eval^₁ c₂)

eval-quote^₁ : (c : n ⟷₁^ m) → eval^₁ (quote^₁ c) ⟷₂^ c
eval-quote^₁ (swap₊^ {n = n}) 
    rewrite (ℕ-p (+-assoc 1 1 n))
    rewrite (ℕ-p (+-unit-r 1)) 
    rewrite (ℕ-p (+-assoc 1 0 1)) = 
        _ ⟷₂^⟨ idl◎l^ ⟩
        _ ⟷₂^⟨ idr◎l^ ⟩   -- id⟷₂^ ⊡^ {! _  !} ⟩
        _ ⟷₂^⟨ ⊕⊕id⟷₁⟷₂^ ⊡^ ((id⟷₂^ ⊡^ ⊕⊕id⟷₁⟷₂^) ⊡^ (⊕⊕id⟷₁⟷₂^ ⊡^ ⊕⊕id⟷₁⟷₂^)) ⟩
        _ ⟷₂^⟨ idl◎l^ ⟩
        _ ⟷₂^⟨ idr◎l^ ⊡^ idl◎l^ ⟩
        _ ⟷₂^⟨ idr◎l^ ⟩
        swap₊^ ⟷₂^∎
eval-quote^₁ id⟷₁^ = id⟷₂^
eval-quote^₁ (c ◎^ c₁) = eval-quote^₁ c ⊡^ eval-quote^₁ c₁
eval-quote^₁ (⊕^ c) with (⟷₁^-eq-size c) 
... | idp = resp⊕⟷₂ (eval-quote^₁ c)

quote-eval^₁ : {t₁ : U n} {t₂ : U m} → (c : t₁ ⟷₁ t₂) → quote^₁ (eval^₁ c) ⟷₂ denorm c
quote-eval^₁ c = TODO
-- quote-eval^₁ {t₁} {.t₁} id⟷₁ = trans⟷₂ linv◎r (id⟷₂ ⊡ idl◎r)