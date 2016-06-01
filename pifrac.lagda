\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module pifrac where

open import Level using () renaming (zero to lzero; suc to lsuc)

open import Data.Product using (∃; Σ; Σ-syntax; ,_; _,_)

open import Universe using (Universe)

open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Categories.Sum using (Sum)
open import Categories.Product using (Product)
open import Categories.Groupoid.Sum using () renaming (Sum to GSum)
open import Categories.Groupoid using () renaming (Product to GProduct)

open import pibackground using (FT; UFT; _⟷_;
  id⟷)
-- open import groupoid using (discreteC)

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{$\Pi^/$}

\begin{code}

postulate -- in groupoid.lagda
  discreteC : Set → Category lzero lzero lzero
  discreteG : (S : Set) → Groupoid (discreteC S)
  orderC : {τ : FT} → (p : τ ⟷ τ) → Category lzero lzero lzero
  orderG : {τ : FT} → (p : τ ⟷ τ) → Groupoid (orderC p)
  1/orderC : {τ : FT} (p : τ ⟷ τ) → Category lzero lzero lzero
  1/orderG : {τ : FT} (p : τ ⟷ τ) → Groupoid (1/orderC p)

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

-- values of type FT/ are a point in the carrier and
-- an automorphism on that point

\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


