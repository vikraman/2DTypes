{-# OPTIONS --without-K --exact-split --rewriting --allow-unsolved-metas #-}

open import lib.Base
open import lib.NType
open import lib.PathFunctor
open import lib.PathGroupoid
open import lib.types.Nat as N renaming (_+_ to _++_)

open import Pi+.Misc as N renaming (_*_ to _**_)
open import Pi+.Extra

module Pi+.Indexed.Translation2 where

open import Pi+.NonIndexed.Syntax as NPi+
open import Pi+.Indexed.Syntax as Pi+
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.Indexed.SyntaxFull as Pi
open import Pi+.Indexed.Equiv1Hat

private
  variable
    m n o p q r : ℕ

private
  variable
    t t₁ t₂ t₃ t₄ t₅ t₆ : Pi.U

-- eval₀-card : Pi.U → ℕ
-- eval₀-card O = O
-- eval₀-card I = S O
-- eval₀-card (t₁ + t₂) = eval₀-card t₁ N.+ eval₀-card t₂
-- eval₀-card (t₁ × t₂) = eval₀-card t₁ N.* eval₀-card t₂


eval₀-card-aux : NPi+.U → ℕ
eval₀-card-aux O = O
eval₀-card-aux I = S O
eval₀-card-aux (t₁ + t₂) = eval₀-card-aux t₁ N.+ eval₀-card-aux t₂

_*_ : NPi+.U → NPi+.U → NPi+.U
O * t₂ = O
I * t₂ = t₂
(t₁ + t₃) * t₂ = (t₁ * t₂) + (t₃ * t₂)

eval₀-card-aux-* : ∀ {t₁ t₂} → eval₀-card-aux (t₁ * t₂) == (eval₀-card-aux t₁) ** (eval₀-card-aux t₂)
eval₀-card-aux-* {O} = idp
eval₀-card-aux-* {I} = ! (N.+-unit-r _)
eval₀-card-aux-* {t₁ = t₁ + t₂} {t₂ = t₄} = 
    let r₁ = eval₀-card-aux-* {t₁} {t₄}
        r₂ = eval₀-card-aux-* {t₂} {t₄}
    in  ap2 (_++_) r₁ r₂ ∙ N.+-distr

eval₀-aux : Pi.U → NPi+.U
eval₀-aux O = O
eval₀-aux I = I
eval₀-aux (t₁ + t₂) = eval₀-aux t₁ + eval₀-aux t₂
eval₀-aux (t₁ × t₂) = eval₀-aux t₁ * eval₀-aux t₂

eval₀ : Pi.U → ℕ
eval₀ t = eval₀-card-aux (eval₀-aux t)

eval₀-index : (t : NPi+.U) → Pi+.U (eval₀-card-aux t)
eval₀-index O = O
eval₀-index I = I
eval₀-index (t + t₁) = eval₀-index t + eval₀-index t₁

eval₀-plus : (t : Pi.U) → Pi+.U (eval₀ t)
eval₀-plus t = eval₀-index (eval₀-aux t)

absorbr* : ∀ {t} → (t * O) NPi+.⟷₁ O
absorbr* {O} = id⟷₁
absorbr* {I} = id⟷₁
absorbr* {t₁ + t₂} = (absorbr* ⊕ absorbr*) ◎ unite₊l

unitr* : ∀ {t} → (t * I) NPi+.⟷₁ t
unitr* {O} = id⟷₁
unitr* {I} = id⟷₁
unitr* {t₁ + t₂} = unitr* ⊕ unitr*

dist* : ∀ {t₁ t₂ t₃} → (t₂ * t₁) + (t₂ * t₃) NPi+.⟷₁ (t₂ * (t₁ + t₃))
dist* {t₁} {O} {t₃} = unite₊l
dist* {t₁} {I} {t₃} = id⟷₁
dist* {t₁} {t₂ + t₄} {t₃} =
    let d₁ = dist* {t₁} {t₂} {t₃}
        d₂ = dist* {t₁} {t₄} {t₃}

        e₁ = (assocr₊ ◎ (id⟷₁ ⊕ assocl₊))
        e₂ = ((id⟷₁ ⊕ assocr₊)) ◎ assocl₊
    in  e₁ ◎ (id⟷₁ ⊕ swap₊ ⊕ id⟷₁) 
        ◎ e₂ ◎ d₁ ⊕ d₂

swap* : ∀ {t₁ t₂} → (t₁ * t₂) NPi+.⟷₁ (t₂ * t₁)
swap* {O} {t₂} = NPi+.!⟷₁ absorbr*
swap* {I} {t₂} = NPi+.!⟷₁ unitr*
swap* {t₁ + t₃} {t₂} = (swap* {t₁} {t₂} ⊕ swap* {t₃} {t₂}) ◎ dist*

eval₁-aux : t₁ Pi.⟷₁ t₂ → eval₀-aux t₁ NPi+.⟷₁ eval₀-aux t₂
eval₁-aux unite₊l = unite₊l
eval₁-aux uniti₊l = uniti₊l
eval₁-aux unite⋆l = id⟷₁
eval₁-aux uniti⋆l = id⟷₁
eval₁-aux swap₊ = swap₊
eval₁-aux (swap⋆ {t₁} {t₂}) = swap* {eval₀-aux t₁} {eval₀-aux t₂}
eval₁-aux assocl₊ = assocl₊
eval₁-aux assocr₊ = assocr₊
eval₁-aux assocl⋆ = TODO!
eval₁-aux assocr⋆ = TODO!
eval₁-aux absorbr = id⟷₁
eval₁-aux absorbl = absorbr*
eval₁-aux factorzr = NPi+.!⟷₁ absorbr*
eval₁-aux factorzl = id⟷₁
eval₁-aux dist = id⟷₁
eval₁-aux factor = id⟷₁
eval₁-aux id⟷₁ = id⟷₁
eval₁-aux (c₁ ◎ c₂) = eval₁-aux c₁ ◎ eval₁-aux c₂
eval₁-aux (c₁ ⊕ c₂) = eval₁-aux c₁ ⊕ eval₁-aux c₂
eval₁-aux (c₁ ⊗ c₂) = TODO!

eval₁-index : ∀ {t₁} {t₂} → (t₁ NPi+.⟷₁ t₂) → eval₀-index t₁ Pi+.⟷₁ eval₀-index t₂
eval₁-index unite₊l = unite₊l
eval₁-index uniti₊l = uniti₊l
eval₁-index swap₊ = swap₊
eval₁-index assocl₊ = assocl₊
eval₁-index assocr₊ = assocr₊
eval₁-index id⟷₁ = id⟷₁
eval₁-index (c ◎ c₁) = eval₁-index c ◎ eval₁-index c₁
eval₁-index (c ⊕ c₁) = eval₁-index c ⊕ eval₁-index c₁

eval₁-plus : ∀ {t₁} {t₂} → (t₁ Pi.⟷₁ t₂) → eval₀-plus t₁ Pi+.⟷₁ eval₀-plus t₂
eval₁-plus = eval₁-index ∘ eval₁-aux

eval₁ : ∀ {t₁} {t₂} → (t₁ Pi.⟷₁ t₂) → eval₀ t₁ Pi^.⟷₁^ eval₀ t₂
eval₁ = eval^₁ ∘ eval₁-index ∘ eval₁-aux