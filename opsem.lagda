\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module opsem where

open import Level using () renaming (zero to l0; suc to lsuc)
open import Universe using (Universe)

open import Data.Product

open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)

open import pibackground 

-- open import groupoid
data FT/ : Set where
  ⇑    : FT → FT/
  #    : {τ : FT} → (p : τ ⟷ τ) → FT/ 
  1/#  : {τ : FT} → (p : τ ⟷ τ) → FT/
  _⊞_  : FT/ → FT/ → FT/              
  _⊠_  : FT/ → FT/ → FT/
postulate
  UG : Universe l0 (lsuc l0)
  ⟦_⟧/ : (T : FT/) → Σ[ ℂ ∈ Category l0 l0 l0 ] (Groupoid ℂ)

\end{code}


}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Operational Semantics} 

%%%%%%%
\subsection{Combinators} 
  
Cardinality-preserving combinators: sound, not complete (see
limitations section), consistent.

\medskip

\begin{code}
-- do the trick of parametrizing the types so that we
-- don't have to repeat the constructors??

infix  30 _⇿_

data _⇿_ : FT/ → FT/ → Set where
  lift : {τ₁ τ₂ : FT} → (p : τ₁ ⟷ τ₂) → (⇑ τ₁ ⇿ ⇑ τ₂)
  η : {τ : FT} {p : τ ⟷ τ} → ⇑ ONE ⇿ (# p ⊠ 1/# p)
  ε : {τ : FT} {p : τ ⟷ τ} → (# p ⊠ 1/# p) ⇿ ⇑ ONE
  unite₊l/ : ∀ {T} → (⇑ ZERO ⊞ T) ⇿ T
  uniti₊l/ : ∀ {T} → T ⇿ (⇑ ZERO ⊞ T) 
  unite₊r/ : ∀ {T} → (T ⊞ ⇑ ZERO) ⇿ T
  uniti₊r/ : ∀ {T} → T ⇿ (T ⊞ ⇑ ZERO)
  swap₊  / : ∀ {T₁ T₂} → (T₁ ⊞ T₂) ⇿ (T₂ ⊞ T₁)
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

%%%%%%%
\subsection{Values}

Values of types FT/ are a pair of a point and automorphism on that
point. Note that the values of $\order{p}$ are things that represent
``apply this program $i$ times''

\medskip

\begin{code}
V : (T : FT/) → Set
V T = let ℂ , _ = ⟦ T ⟧/
          open Category ℂ
      in Σ[ v ∈ Obj ] (v ⇒ v)
\end{code}

%%%%%%%
\subsection{Interpreter}

\begin{code}
ap/ : {T₁ T₂ : FT/} → (T₁ ⇿ T₂) → V T₁ → V T₂
ap/ {⇑ τ₁} {⇑ τ₂} (lift p) (v , av) = {!!} , {!!}
ap/ η (v , av) = {!!}
ap/ ε (v , av) = {!!}
ap/ unite₊l/ (v , av) = {!!}
ap/ uniti₊l/ (v , av) = {!!}
ap/ unite₊r/ (v , av) = {!!}
ap/ uniti₊r/ (v , av) = {!!}
ap/ swap₊ (v , av) = {!!}
ap/ / (v , av) = {!!}
ap/ assocl₊/ (v , av) = {!!}
ap/ assocr₊/ (v , av) = {!!}
ap/ unite⋆l/ (v , av) = {!!}
ap/ uniti⋆l/ (v , av) = {!!}
ap/ unite⋆r/ (v , av) = {!!}
ap/ uniti⋆r/ (v , av) = {!!}
ap/ swap⋆/ (v , av) = {!!}
ap/ assocl⋆/ (v , av) = {!!}
ap/ assocr⋆/ (v , av) = {!!}
ap/ absorbr/ (v , av) = {!!}
ap/ absorbl/ (v , av) = {!!}
ap/ factorzr/ (v , av) = {!!}
ap/ factorzl/ (v , av) = {!!}
ap/ dist/ (v , av) = {!!}
ap/ factor/ (v , av) = {!!}
ap/ distl/ (v , av) = {!!}
ap/ factorl/ (v , av) = {!!}
ap/ id⇿ (v , av) = (v , av)
ap/ (c₁ ◎/ c₂) (v , av) = {!!}
ap/ (c₁ ⊕/ c₂) (v , av) = {!!}
ap/ (c₁ ⊗/ c₂) (v , av) = {!!} 
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

