{-# OPTIONS --without-K --exact-split --rewriting --allow-unsolved-metas #-}

open import lib.Base
open import lib.NType
open import lib.PathFunctor
open import lib.PathGroupoid
open import lib.types.Nat as N renaming (_+_ to _++_)

open import Pi+.Misc as N renaming (_*_ to _**_)
open import Pi+.Extra

module Pi+.Indexed.Translation2 where

open import Pi+.NonIndexed.Syntax as Pi+
open import Pi+.Indexed.SyntaxFull as Pi

private
  variable
    m n o p q r : ℕ

private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : Pi.U

eval₀-aux : Pi.U → ℕ
eval₀-aux O = O
eval₀-aux I = S O
eval₀-aux (t₁ + t₂) = eval₀-aux t₁ N.+ eval₀-aux t₂
eval₀-aux (t₁ × t₂) = eval₀-aux t₁ N.* eval₀-aux t₂

_*_ : Pi+.U → Pi+.U → Pi+.U
O * t₂ = O
I * t₂ = t₂
(t₁ + t₃) * t₂ = (t₁ * t₂) + (t₃ * t₂)

eval₀ : Pi.U → Pi+.U
eval₀ O = O
eval₀ I = I
eval₀ (t₁ + t₂) = eval₀ t₁ + eval₀ t₂
eval₀ (t₁ × t₂) = eval₀ t₁ * eval₀ t₂

absorbr* : ∀ {t} → (t * O) Pi+.⟷₁ O
absorbr* {O} = id⟷₁
absorbr* {I} = id⟷₁
absorbr* {t₁ + t₂} = (absorbr* ⊕ absorbr*) ◎ unite₊l

unitr* : ∀ {t} → (t * I) Pi+.⟷₁ t
unitr* {O} = id⟷₁
unitr* {I} = id⟷₁
unitr* {t₁ + t₂} = unitr* ⊕ unitr*

distr* : ∀ {t₁ t₂ t₃} → ((t₁ + t₃) * t₂) Pi+.⟷₁ (t₁ * t₂) + (t₃ * t₂)
distr* {t₁} {t₂} {t₃} = {!!}

dist* : ∀ {t₁ t₂ t₃} → (t₂ * t₁) + (t₂ * t₃) Pi+.⟷₁ (t₂ * (t₁ + t₃))
dist* {t₁} {O} {t₃} = unite₊l
dist* {t₁} {I} {t₃} = id⟷₁
dist* {t₁} {t₂ + t₄} {t₃} =
  let c₁ = distr* {t₁} {t₂} {t₃}
      c₂ = distr* {t₁} {t₄} {t₃}
  in {!!} ◎ {!!}

swap* : ∀ {t₁ t₂} → (t₁ * t₂) Pi+.⟷₁ (t₂ * t₁)
swap* {O} {t₂} = Pi+.!⟷₁ absorbr*
swap* {I} {t₂} = Pi+.!⟷₁ unitr*
swap* {t₁ + t₃} {t₂} = (swap* {t₁} {t₂} ⊕ swap* {t₃} {t₂}) ◎ {!!}

eval₁ : t₁ Pi.⟷₁ t₂ → eval₀ t₁ Pi+.⟷₁ eval₀ t₂
eval₁ unite₊l = unite₊l
eval₁ uniti₊l = uniti₊l
eval₁ unite⋆l = id⟷₁
eval₁ uniti⋆l = id⟷₁
eval₁ swap₊ = swap₊
eval₁ swap⋆ = {!!}
eval₁ assocl₊ = assocl₊
eval₁ assocr₊ = assocr₊
eval₁ assocl⋆ = {!!}
eval₁ assocr⋆ = {!!}
eval₁ absorbr = id⟷₁
eval₁ absorbl = {!!}
eval₁ factorzr = {!!}
eval₁ factorzl = id⟷₁
eval₁ dist = {!!}
eval₁ factor = {!!}
eval₁ id⟷₁ = id⟷₁
eval₁ (c₁ ◎ c₂) = eval₁ c₁ ◎ eval₁ c₂
eval₁ (c₁ ⊕ c₂) = eval₁ c₁ ⊕ eval₁ c₂
eval₁ (c₁ ⊗ c₂) = {!!}
