{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.notes.Claim where

open import Pi+.Syntax

pp1 : (I + I) + (I + I) ⟷₁ (I + I) + (I + I)
pp1 = swap₊ ⊕ (id⟷₁ ⊕ id⟷₁)

pp2 : (I + I) + (I + I) ⟷₁ (I + I) + (I + I)
pp2 = (id⟷₁ ⊕ id⟷₁) ⊕ swap₊

-- This combinator corresponds, in a way, to `swap` relation in Coxeter presentation
-- In the special case of Fin 4, it shows that unrelated swaps can be (sequentially) exchanged
-- The proof is a version of Eckmann-Hilton argument - maybe it will be useful later?

Claimp : pp1 ◎ pp2 ⟷₂ pp2 ◎ pp1
Claimp = trans⟷₂ hom◎⊕⟷₂ (trans⟷₂ (resp⊕⟷₂ swapl₊⟷₂ swapr₊⟷₂) hom⊕◎⟷₂)

-- This combinator is should in some way correspond to `braid` relation in Coxeter presentation
-- In the special case of Fin 4, it shows that three overlapping swaps can be braided, e.g. 010 = 101
-- It's a translation of a diagram on p. 4 in "Pi Semantics.pdf" document.

qq1 : I + (I + I) ⟷₁ I + (I + I)
qq1 = (id⟷₁ ⊕ swap₊) ◎ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊ ◎ (id⟷₁ ⊕ swap₊)

qq2 : I + (I + I) ⟷₁ I + (I + I)
qq2 = assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊ ◎ (id⟷₁ ⊕ swap₊) ◎ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊

Claimq : qq1 ⟷₂ qq2
Claimq = {!   !}

-- The claim is that these two operators should somehow "generate" all others in Pi (up to adding associativity etc).
-- However, the question is, how to express interpret/express them in the language of free symmetric monoidal groupoids
-- (The first one is naturality of swap)
-- (The other one should be something like a composition of hexagons)
