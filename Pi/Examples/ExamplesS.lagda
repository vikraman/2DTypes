\begin{code}[hide]
{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}
module Pi.Examples.ExamplesS where

open import HoTT hiding (_<_ ; ltS ; ltSR ; _+_ ; _×_)
import lib.types.Nat as N
import lib.types.Sigma as S

open import Pi.UFin.BAut
open import Pi.Common.Misc
open import Pi.Common.Extra

open import Pi.Syntax.Pi+.Indexed as Pi+
  renaming (_⟷₁_ to _⟷₁₊_; _⟷₂_ to _⟷₂₊_; !⟷₁ to !⟷₁₊; U to U+;
  idr◎l to idr◎l+; swapl₊⟷₂ to swapl₊⟷₂+; unite₊r to unite₊r+)
open import Pi.Syntax.Pi^ as Pi^
open import Pi.Syntax.Pi^Helpers as Pi^
open import Pi.Syntax.Pi as Pi hiding (_⟷₂_)
open import Pi.Equiv.Translation2
import Pi.Equiv.Equiv1 as Pi+
import Pi.Equiv.Equiv0Hat as Pi^
import Pi.Equiv.Equiv1Hat as Pi^
import Pi.Equiv.Equiv0Norm as Pi^
import Pi.Equiv.Equiv1Norm as Pi^
open import Pi.UFin.UFin
open import Pi.UFin.Monoidal
open import Pi.Common.FinHelpers
open import Pi.Lehmer.FinExcept

open import Pi.Examples.Base

private
  variable
    t A B C D E F X Y : Pi.U
    c₁ c₂ c₃ : A Pi.⟷₁ B
\end{code}

\newcommand{\controlled}{%
\begin{code}
controlled : (c : A ⟷₁ A) → (𝟚 × A ⟷₁ 𝟚 × A)
controlled c = dist ◎ ((id⟷₁ ⊗ c) ⊕ id⟷₁) ◎ factor
\end{code}
}

\newcommand{\cnot}{%
\begin{code}
not : 𝟚 ⟷₁ 𝟚
not = swap₊

cnot : 𝟚 × 𝟚 ⟷₁ 𝟚 × 𝟚
cnot = controlled not
\end{code}
}

\newcommand{\toffolithree}{%
\begin{code}
toffoli₃ : 𝟚 × (𝟚 × 𝟚) ⟷₁ 𝟚 × (𝟚 × 𝟚)
toffoli₃ = controlled cnot
\end{code}
}

\begin{code}[hide]
data _⟷₂_ : {X : U} {Y : U} → X ⟷₁ Y → X ⟷₁ Y → Set where
\end{code}

\newcommand{\leveltwoblockone}{%
\begin{code}
  assoc◎l   : (c₁ ◎ (c₂ ◎ c₃)) ⟷₂ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r   : ((c₁ ◎ c₂) ◎ c₃) ⟷₂ (c₁ ◎ (c₂ ◎ c₃))
  assocl₊l  : ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊) ⟷₂ (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃))
  assocl₊r  : (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃)) ⟷₂ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊)
  assocr₊r  : (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊) ⟷₂ (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃)))
  assocr₊l  : (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃))) ⟷₂ (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊)
\end{code}}
