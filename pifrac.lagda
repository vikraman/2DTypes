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

combinators between FT/ types including eta and epsilon

proof that combinators are information preserving

other properties: inverses etc.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


