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

open import pibackground 
open import groupoid 

infix  30 _⇿_

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{$\Pi^/$}

combinators between FT/ types including eta and epsilon

proof that combinators are information preserving

other properties: inverses etc.

Cardinality-preserving combinators: sound, not complete (see
limitations section), consistent.

\medskip

\begin{code}
data _⇿_ : FT/ → FT/ → Set where
  lift : {τ₁ τ₂ : FT} → (p : τ₁ ⟷ τ₂) → (⇑ τ₁ ⇿ ⇑ τ₂)
  η : {τ : FT} → (p : τ ⟷ τ) → ⇑ ONE ⇿ (# p ⊠ 1/# p)
  ε : {τ : FT} → (p : τ ⟷ τ) → (# p ⊠ 1/# p) ⇿ ⇑ ONE
  unite₊l/ : ∀ {T} → (⇑ ZERO ⊞ T) ⇿ T
  uniti₊l/ : ∀ {T} → T ⇿ (⇑ ZERO ⊞ T) 
  unite₊r/ : ∀ {T} → (T ⊞ ⇑ ZERO) ⇿ T
  uniti₊r/ : ∀ {T} → T ⇿ (T ⊞ ⇑ ZERO)
  swap₊/ : ∀ {T₁ T₂} → (T₁ ⊞ T₂) ⇿ (T₂ ⊞ T₁)
  assocl₊/ : ∀ {T₁ T₂ T₃} →
    (T₁ ⊞ (T₂ ⊞ T₃)) ⇿ ((T₁ ⊞ T₂) ⊞ T₃)
  assocr₊/ : ∀ {T₁ T₂ T₃} →
    ((T₁ ⊞ T₂) ⊞ T₃) ⇿ (T₁ ⊞ (T₂ ⊞ T₃))
  unite⋆l/  : ∀ {T} → (⇑ ONE ⊠ T) ⇿ T
  uniti⋆l/  : ∀ {T} → T ⇿ (⇑ ONE ⊠ T)
  unite⋆r/ : ∀ {T} → (T ⊠ ⇑ ONE) ⇿ T
  uniti⋆r/ : ∀ {T} → T ⇿ (T ⊠ ⇑ ONE)
  swap⋆/   : ∀ {T₁ T₂} → (T₁ ⊠ T₂) ⇿ (T₂ ⊠ T₁)
  assocl⋆/ : ∀ {T₁ T₂ T₃} →
    (T₁ ⊠ (T₂ ⊠ T₃)) ⇿ ((T₁ ⊠ T₂) ⊠ T₃)
  assocr⋆/ : ∀ {T₁ T₂ T₃} →
    ((T₁ ⊠ T₂) ⊠ T₃) ⇿ (T₁ ⊠ (T₂ ⊠ T₃))
  absorbr/ : ∀ {T} → (⇑ ZERO ⊠ T) ⇿ ⇑ ZERO
  absorbl/ : ∀ {T} → (T ⊠ ⇑ ZERO) ⇿ ⇑ ZERO
  factorzr/ : ∀ {T} → ⇑ ZERO ⇿ (T ⊠ ⇑ ZERO)
  factorzl/ : ∀ {T} → ⇑ ZERO ⇿ (⇑ ZERO ⊠ T)
  dist/    : ∀ {T₁ T₂ T₃} → 
    ((T₁ ⊞ T₂) ⊠ T₃) ⇿ ((T₁ ⊠ T₃) ⊞ (T₂ ⊠ T₃))
  factor/  : ∀ {T₁ T₂ T₃} → 
    ((T₁ ⊠ T₃) ⊞ (T₂ ⊠ T₃)) ⇿ ((T₁ ⊞ T₂) ⊠ T₃)
  distl/   : ∀ {T₁ T₂ T₃} →
    (T₁ ⊠ (T₂ ⊞ T₃)) ⇿ ((T₁ ⊠ T₂) ⊞ (T₁ ⊠ T₃))
  factorl/ : ∀ {T₁ T₂ T₃} →
    ((T₁ ⊠ T₂) ⊞ (T₁ ⊠ T₃)) ⇿ (T₁ ⊠ (T₂ ⊞ T₃))
  id⇿    : ∀ {T} → T ⇿ T
  _◎/_     : ∀ {T₁ T₂ T₃} → (T₁ ⇿ T₂) → (T₂ ⇿ T₃) → (T₁ ⇿ T₃)
  _⊕/_     : ∀ {T₁ T₂ T₃ T₄} → 
    (T₁ ⇿ T₃) → (T₂ ⇿ T₄) → ((T₁ ⊞ T₂) ⇿ (T₃ ⊞ T₄))
  _⊗/_     : ∀ {T₁ T₂ T₃ T₄} → 
    (T₁ ⇿ T₃) → (T₂ ⇿ T₄) → ((T₁ ⊠ T₂) ⇿ (T₃ ⊠ T₄))
\end{code}

\medskip

Consistency is defined in the following sense: If we allow arbitrary
functions then bad things happen as we can throw away the negative
information for example. In our reversible information-preserving
framework, the theory is consistent in the sense that not all types
are identified. This is easy to see as we only identify types that
have the same cardinality. This is evident for all the combinators
except for the new ones. For those new ones the only subtle situation
is with the empty type. Note however that there is no way to define
1/0 and no permutation has order 0. For 0 we have one permutation id
which has order 1. So if we try to use it, we will map 1 to 1 times
1/id which is fine. So if we always preserve types and trivially 1 and
0 have different cardinalities so there is no way to identify them and
we are consistent.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


