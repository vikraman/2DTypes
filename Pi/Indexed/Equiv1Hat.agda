{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi.Indexed.Equiv1Hat where

open import Pi.Syntax.Pi+.Indexed as Pi
open import Pi.Syntax.Pi^ as Pi^
open import Pi.Syntax.Pi^Helpers as Pi^
open import Pi.UFin
open import Pi.Extra

open import Pi.Indexed.Equiv0Hat

open import lib.Basics
open import lib.types.Fin
open import lib.types.List
open import lib.types.BAut
open import lib.types.Nat as N renaming (_+_ to _+N_)
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct
open import lib.types.Sigma


private
    variable
        n m o : ℕ
        t₁ t₂ t₃ t₄ : U n

quote^₁ : (n ⟷₁^ m) → (quote^₀ n ⟷₁ quote^₀ m)
quote^₁ swap₊^ = assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊
quote^₁ id⟷₁^ = id⟷₁
quote^₁ (c₁ ◎^ c₂) = quote^₁ c₁ ◎ quote^₁ c₂
quote^₁ (⊕^ c₁) = id⟷₁ ⊕ quote^₁ c₁

denorm : {t₁ : U n} {t₂ : U m} → (c : t₁ ⟷₁ t₂) → quote^₀ (eval^₀ t₁) ⟷₁ quote^₀ (eval^₀ t₂)
denorm {t₁ = t₁} {t₂ = t₂} c = (quote-eval^₀ t₁ ◎ c ◎ !⟷₁ (quote-eval^₀ t₂))

denorm-⊕-β : (c₁ : t₁ ⟷₁ t₂) → (c₂ : t₃ ⟷₁ t₄)
    → denorm (c₁ ⊕ c₂) ⟷₂ (quote^₀++ _ _ ◎ ((denorm c₁) ⊕ (denorm c₂)) ◎ !⟷₁ (quote^₀++ _ _))
denorm-⊕-β c₁ c₂ = !⟷₂ (
    _ ⟷₂⟨ assoc◎l ⟩
    _ ⟷₂⟨ (id⟷₂ ⊡  hom⊕◎⟷₂) ⊡ id⟷₂ ⟩
    _ ⟷₂⟨ (id⟷₂ ⊡ (id⟷₂ ⊡ hom⊕◎⟷₂)) ⊡ id⟷₂ ⟩
    _ ⟷₂⟨ assoc◎l ⊡ id⟷₂ ⟩
    _ ⟷₂⟨ assoc◎r ⟩
    _ ⟷₂⟨ id⟷₂ ⊡ assoc◎r ⟩
    _ ⟷₂∎)

denorm-◎-β : {t₁ : U n} {t₂ : U m} {t₃ : U o} → (c₁ : t₁ ⟷₁ t₂) → (c₂ : t₂ ⟷₁ t₃) → denorm (c₁ ◎ c₂) ⟷₂ (denorm c₁) ◎ (denorm c₂)
denorm-◎-β c₁ c₂ = !⟷₂ (
    _ ⟷₂⟨ assoc◎l ⟩
    _ ⟷₂⟨ assoc◎r ⊡ id⟷₂ ⟩
    _ ⟷₂⟨ (id⟷₂ ⊡ assoc◎r) ⊡ id⟷₂ ⟩
    _ ⟷₂⟨ (id⟷₂ ⊡ (id⟷₂ ⊡ rinv◎l)) ⊡ id⟷₂ ⟩
    _ ⟷₂⟨ (id⟷₂ ⊡ idr◎l) ⊡ id⟷₂ ⟩
    _ ⟷₂⟨ assoc◎r ⟩
    _ ⟷₂⟨ id⟷₂ ⊡ assoc◎l ⟩
    _ ⟷₂∎)

denorm← : {t₁ : U n} {t₂ : U m} → (c : quote^₀ (eval^₀ t₁) ⟷₁ quote^₀ (eval^₀ t₂)) → t₁ ⟷₁ t₂
denorm← {t₁ = t₁} {t₂ = t₂} c = (!⟷₁ (quote-eval^₀ t₁)) ◎ c ◎ (quote-eval^₀ t₂)

eval^₁ : {t₁ : U n} {t₂ : U m} → (t₁ ⟷₁ t₂) → (eval^₀ t₁ ⟷₁^ eval^₀ t₂)
eval^₁ unite₊l = id⟷₁^
eval^₁ uniti₊l = id⟷₁^
eval^₁ (swap₊ {t₁ = t₁} {t₂ = t₂}) = ++^-swap (eval^₀ t₁) (eval^₀ t₂)
eval^₁ (assocl₊ {n} {t₁ = t₁} {m} {t₂ = t₂} {o} {t₃ = t₃}) = !⟷₁^ (++^-assoc (eval^₀ t₁) (eval^₀ t₂) (eval^₀ t₃))
eval^₁ (assocr₊ {n} {t₁ = t₁} {m} {t₂ = t₂} {o} {t₃ = t₃}) = ++^-assoc (eval^₀ t₁) (eval^₀ t₂) (eval^₀ t₃)
eval^₁ id⟷₁ = id⟷₁^
eval^₁ (c₁ ◎ c₂) = eval^₁ c₁ ◎^ eval^₁ c₂
eval^₁ (c₁ ⊕ c₂) = ++^-⊕ (eval^₁ c₁) (eval^₁ c₂)

eval-quote^₁ : (c : n ⟷₁^ m) → eval^₁ (quote^₁ c) ⟷₂^ c
eval-quote^₁ (swap₊^ {n = n}) =
        _ ⟷₂^⟨ ⊕id⟷₁⟷₂^ ⊡^ (((⊕⊕id⟷₁⟷₂^ ⊡^ ((id⟷₂^ ⊡^ ⊕⊕id⟷₁⟷₂^) ⊡^ (⊕⊕id⟷₁⟷₂^ ⊡^ ⊕⊕id⟷₁⟷₂^)))) ⊡^ ⊕id⟷₁⟷₂^) ⟩
        _ ⟷₂^⟨ idl◎l^ ⟩
        _ ⟷₂^⟨ idr◎l^ ⟩
        _ ⟷₂^⟨ idl◎l^ ⟩
        _ ⟷₂^⟨ id⟷₂^ ⊡^ idl◎l^ ⟩
        _ ⟷₂^⟨ idr◎l^ ⟩
        _ ⟷₂^⟨ idr◎l^ ⟩
        swap₊^ ⟷₂^∎
eval-quote^₁ id⟷₁^ = id⟷₂^
eval-quote^₁ (c₁ ◎^ c₂) = eval-quote^₁ c₁ ⊡^ eval-quote^₁ c₂
eval-quote^₁ (⊕^ c) with (⟷₁^-eq-size c)
... | idp = resp⊕⟷₂ (eval-quote^₁ c)

quote-eval^₁ : {t₁ : U n} {t₂ : U m} → (c : t₁ ⟷₁ t₂) → quote^₁ (eval^₁ c) ⟷₂ denorm c
quote-eval^₁ unite₊l = !⟷₂ ((uniti₊l⟷₂l ⊡ id⟷₂) ■ linv◎l)
quote-eval^₁ uniti₊l = !⟷₂ ((id⟷₂ ⊡ (id⟷₂ ⊡ unite₊l⟷₂r)) ■ (assoc◎l ■ linv◎l))
quote-eval^₁ swap₊ = !⟷₂ (
    _ ⟷₂⟨ (id⟷₂ ⊡ assoc◎l) ⟩
    _ ⟷₂⟨ (id⟷₂ ⊡ (swapl₊⟷₂ ⊡ id⟷₂)) ⟩
    _ ⟷₂⟨ assoc◎r ⟩
    _ ⟷₂⟨ id⟷₂ ⊡ (id⟷₂ ⊡  assoc◎r) ⟩
    _ ⟷₂⟨ id⟷₂ ⊡ assoc◎l ⟩
    _ ⟷₂⟨ id⟷₂ ⊡ (linv◎l ⊡ id⟷₂) ⟩
    _ ⟷₂⟨ id⟷₂ ⊡ idl◎l ⟩
    _ ⟷₂⟨ TODO! ⟩
    _ ⟷₂∎)
quote-eval^₁ assocl₊ = TODO!
quote-eval^₁ assocr₊ = TODO!
quote-eval^₁ id⟷₁ = linv◎r ■ (id⟷₂ ⊡ idl◎r)
quote-eval^₁ (c₁ ◎ c₂) =
    let r₁ = quote-eval^₁ c₁
        r₂ = quote-eval^₁ c₂
    in _ ⟷₂⟨ (r₁ ⊡ r₂) ⟩
       _ ⟷₂⟨ !⟷₂ (denorm-◎-β _ _) ⟩
       _ ⟷₂∎
quote-eval^₁ (c₁ ⊕ c₂) =
    let r₁ = !⟷₂ (quote-eval^₁ c₁)
        r₂ = !⟷₂ (quote-eval^₁ c₂)
    in !⟷₂ (
       _ ⟷₂⟨ denorm-⊕-β _ _ ⟩
       _ ⟷₂⟨ (id⟷₂ ⊡ (resp⊕⟷₂ r₁ r₂ ⊡ id⟷₂)) ⟩
       _ ⟷₂⟨ TODO! ⟩
       _ ⟷₂∎)
