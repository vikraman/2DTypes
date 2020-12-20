{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Claim where

open import Pi+.Syntax

pp1 : (I + I) + (I + I) ⟷₁ (I + I) + (I + I)
pp1 = swap₊ ⊕ (id⟷₁ ⊕ id⟷₁)

pp2 : (I + I) + (I + I) ⟷₁ (I + I) + (I + I)
pp2 = (id⟷₁ ⊕ id⟷₁) ⊕ swap₊

Claimp : pp1 ◎ pp2 ⟷₂ pp2 ◎ pp1
Claimp = trans⟷₂ hom◎⊕⟷₂ (trans⟷₂ (resp⊕⟷₂ swapl₊⟷₂ swapr₊⟷₂) hom⊕◎⟷₂)

qq1 : I + (I + I) ⟷₁ I + (I + I)
qq1 = (id⟷₁ ⊕ swap₊) ◎ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊ ◎ (id⟷₁ ⊕ swap₊)

qq2 : I + (I + I) ⟷₁ I + (I + I)
qq2 = assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊ ◎ (id⟷₁ ⊕ swap₊) ◎ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊

Claimq : qq1 ⟷₂ qq2
Claimq = {!   !}


-- qq1 : (I + I) + I ⟷₁ (I + I) + I
-- qq1 = swap₊ ⊕ id⟷₁

-- qq2 : (I + I) + I ⟷₁ (I + I) + I
-- qq2 = {!  !}

-- NotClaim : qq1 ◎ qq2 ⟷₂ qq2 ◎ qq1
-- NotClaim = {!   !}