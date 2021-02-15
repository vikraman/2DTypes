{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.Indexed.Equiv0Hat where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.UFin
open import Pi+.Extra

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
    n m o p : ℕ

_++^_ : U^ m → U^ n → U^ (m N.+ n)
O ++^ t₂ = t₂
(I+ t₁) ++^ t₂ = I+ (t₁ ++^ t₂)

++^-unit : {t : U^ m} → t ⟷₁^ (t ++^ O)
++^-unit {t = O} = id⟷₁^
++^-unit {t = I+ t} = ⊕^ ++^-unit {t = t}

++^-assoc : (t₁ : U^ m) (t₂ : U^ n) (t₃ : U^ o) → (t₁ ++^ (t₂ ++^ t₃)) ⟷₁^ ((t₁ ++^ t₂) ++^ t₃)
++^-assoc O t₂ t₃ = id⟷₁^
++^-assoc (I+ t₁) t₂ t₃ = ⊕^ ++^-assoc t₁ t₂ t₃

++^-cons : (t : U^ n) → I+ t ⟷₁^ (t ++^ (I+ O))
++^-cons O = id⟷₁^
++^-cons (I+ t) = swap₊^ ◎^ (⊕^ (++^-cons t))

++^-⊕ : {t₁ : U^ m} {t₂ : U^ n} {t₃ : U^ o} {t₄ : U^ p} → (t₁ ⟷₁^ t₂) → (t₃ ⟷₁^ t₄) → (t₁ ++^ t₃) ⟷₁^ (t₂ ++^ t₄)
++^-⊕ (swap₊^ {t = t}) c₂ = big-swap₊^ (++^-⊕ (id⟷₁^ {t = t}) c₂)
++^-⊕ {t₁ = O} id⟷₁^ c₂ = c₂
++^-⊕ {t₁ = I+ t₁} id⟷₁^ c₂ = ⊕^ (++^-⊕ id⟷₁^ c₂)
++^-⊕ (c₁ ◎^ c₃) c₂ = (++^-⊕ c₁ c₂) ◎^ ++^-⊕ c₃ id⟷₁^
++^-⊕ (⊕^ c₁) c₂ = ⊕^ (++^-⊕ c₁ c₂)

++^-swap : (t₁ : U^ m) (t₂ : U^ n) → (t₁ ++^ t₂) ⟷₁^ (t₂ ++^ t₁)
++^-swap O t₂ = ++^-unit {t = t₂}
++^-swap (I+ t₁) t₂ = (⊕^ ++^-swap t₁ t₂) ◎^ ++^-cons (t₂ ++^ t₁) ◎^ !⟷₁^ (++^-assoc t₂ t₁ (I+ O)) ◎^ ++^-⊕ id⟷₁^ (!⟷₁^ (++^-cons t₁))

quote^₀ : U^ n → U n
quote^₀ O = O
quote^₀ (I+ X) = I U.+ quote^₀ X

quote^₀++ : (t₁ : U^ n) (t₂ : U^ m) → quote^₀ (t₁ ++^ t₂) ⟷₁ quote^₀ t₁ U.+ quote^₀ t₂
quote^₀++ O t₂ = uniti₊l
quote^₀++ (I+ t₁) t₂ = (id⟷₁ ⊕ quote^₀++ t₁ t₂) ◎ assocl₊

eval^₀ : U n → U^ n
eval^₀ O = O
eval^₀ I = I+ O
eval^₀ (t₁ U.+ t₂) = eval^₀ t₁ ++^ eval^₀ t₂

quote-eval^₀ : (t : U n) → quote^₀ (eval^₀ t) ⟷₁ t
quote-eval^₀ O = id⟷₁
quote-eval^₀ I = swap₊ ◎ unite₊l
quote-eval^₀ (t₁ U.+ t₂) = quote^₀++ (eval^₀ t₁) (eval^₀ t₂) ◎ (quote-eval^₀ t₁ ⊕ quote-eval^₀ t₂)

eval-quote^==₀ : (t : U^ n) → eval^₀ (quote^₀ t) == t
eval-quote^==₀ O = idp
eval-quote^==₀ (I+ t) = ap I+_ (eval-quote^==₀ t)

eval-quote^₀ : (t : U^ n) → eval^₀ (quote^₀ t) ⟷₁^ t
eval-quote^₀ O = id⟷₁^
eval-quote^₀ (I+ t) = ⊕^ eval-quote^₀ t

postulate
    eval-quote₀-rewrite : {t : U^ n} → (eval^₀ (quote^₀ t)) ↦ t -- because eval-quote^==₀
    {-# REWRITE eval-quote₀-rewrite #-}

quote-eval²₀ : (t : U n) → quote-eval^₀ (quote^₀ (eval^₀ t)) ⟷₂ id⟷₁
quote-eval²₀ O = id⟷₂
quote-eval²₀ I = TODO
quote-eval²₀ (t U.+ t₁) = TODO