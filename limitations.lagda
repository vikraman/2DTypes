\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module limitations where

open import Level using () renaming (zero to l0; suc to lsuc)

open import Data.Nat
open import Data.Product using (Σ; Σ-syntax; _,_; ∃; ,_)

open import Universe using (Universe; Indexed-universe)

open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Categories.Groupoid.Sum using () renaming (Sum to GSum)
open import Categories.Groupoid using () renaming (Product to GProduct)

open import pibackground
-- open import groupoid
data FT/ : Set where
  ⇑    : FT → FT/
  #    : {τ : FT} → (p : τ ⟷ τ) → FT/ 
  1/#  : {τ : FT} → (p : τ ⟷ τ) → FT/
  _⊞_  : FT/ → FT/ → FT/              
  _⊠_  : FT/ → FT/ → FT/
postulate
  ⟦_⟧/ : (T : FT/) → Σ[ ℂ ∈ Category l0 l0 l0 ] (Groupoid ℂ)
  discreteC : Set → Category l0 l0 l0
  discreteG : (S : Set) → Groupoid (discreteC S)
  orderC : {τ : FT} → (p : τ ⟷ τ) → Category l0 l0 l0
  orderG : {τ : FT} → (p : τ ⟷ τ) → Groupoid (orderC p)
  1/orderC : {τ : FT} (p : τ ⟷ τ) → Category l0 l0 l0
  1/orderG : {τ : FT} (p : τ ⟷ τ) → Groupoid (1/orderC p)
\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Limitations} 

Given any non-negative rational number, we can form a type whose
cardinality is that number. And yet, our types do not capture the full
structure of the non-negative rational numbers as these form a
commutative semifield. What we are missing is a multiplicative inverse
for every type not just $\order{p}$.

Focusing on the special case we do have, we see that the
multiplicative inverse of $\order{p}$ was obtained by promoting the
objects in $\order{p}$ to morphisms in $1/\hash p$, which is a general
process called \emph{delooping}. It is clear we can go in the inverse
direction by demoting morphisms to objects which is a process called
\emph{looping}. So it seems there is a general process for inverting
arbitraty groupoids in our universe.

The problem is that we cannot do this compositionally: say we have
$\order{p_1}$ and $\order{p_2}$ and we deloop each to get $1/\hash
p_1$ and $1/\hash p_2$ or cardinalities $\frac{1}{\order{p_1}}$ and
$\frac{1}{\order{p_2}}$ respectively. Now say we construct
$\order{p_1} \boxplus \order{p_2}$, we want the delooping to construct
a space with cardinality $\frac{1}{\order{p_1}+\order{p_2}}$ but that
has nothing to do with the individual deloopings.

\begin{code}

-- data FT/ : Set where
--   ⇑   : FT → FT/    
--   #   : {τ : FT} → (p : τ ⟷ τ) → FT/ 
--   1/  : FT/ → FT/
--   _⊞_ : FT/ → FT/ → FT/              
--   _⊠_ : FT/ → FT/ → FT/              

-- ⟦_⟧/ : FT/ → ∃ Groupoid
-- ⟦ ⇑ S ⟧/ = , discreteG (El S) where open Universe.Universe UFT  
-- ⟦ # p ⟧/ = , orderG p
-- ⟦ 1/ (⇑ S) ⟧/ = , 1/orderG {S} {!!}
-- -- need cyclic permutation
-- ⟦ 1/ (# p) ⟧/ = , 1/orderG p
-- ⟦ 1/ (1/ T) ⟧/ = ⟦ T ⟧/
-- ⟦ 1/ (T₁ ⊞ T₂) ⟧/ = {!!}
-- -- extract p₁ from T₁
-- -- extract p₂ from T₂
-- ⟦ 1/ (T₁ ⊠ T₂) ⟧/ with ⟦ 1/ T₁ ⟧/ | ⟦ 1/ T₂ ⟧/
-- ... | (_ , G₁) | (_ , G₂) = , GProduct G₁ G₂
-- ⟦ T₁ ⊞ T₂ ⟧/ with ⟦ T₁ ⟧/ | ⟦ T₂ ⟧/
-- ... | (_ , G₁) | (_ , G₂) = , GSum G₁ G₂
-- ⟦ T₁ ⊠ T₂ ⟧/ with ⟦ T₁ ⟧/ | ⟦ T₂ ⟧/
-- ... | (_ , G₁) | (_ , G₂) = , GProduct G₁ G₂

-- extract underlying permutations from a type

-- data #P : Set where
--   #one : {τ : FT} → (p : τ ⟷ τ) → #P
--   _#+_ : #P → #P → #P
--   _#*_ : #P → #P → #P

-- data FT#/ : Set where
--   #⇑    : FT → FT#/
--   ##    : {τ : FT} → (p : τ ⟷ τ) → FT#/
--   #1/    : FT#/ → FT#/
--   _#⊞_  : FT#/ → FT#/ → FT#/
--   _#⊠_  : FT#/ → FT#/ → FT#/

-- extractP : FT#/ → #P
-- extractP (#⇑ τ) = #one {τ} id⟷
-- extractP (## p) = #one p
-- extractP (#1/ p) = {!!}
-- extractP (T₁ #⊞ T₂) = extractP T₁ #+ extractP T₂ 
-- extractP (T₁ #⊠ T₂) = extractP T₁ #* extractP T₂ 

-- #UG : Universe l0 (lsuc l0)
-- #UG = record {
--         U = FT#/
--       ; El = λ T → Σ[ ℂ ∈ Category l0 l0 l0 ] (Groupoid ℂ)
--       }

-- ⟦_⟧#/ : (T : FT#/) → Universe.El #UG T
-- ⟦ T ⟧#/ = G (extractP T)
--   where G : #P → Σ[ ℂ ∈ Category l0 l0 l0 ] (Groupoid ℂ)
--         G = {!!} 
\end{code}
