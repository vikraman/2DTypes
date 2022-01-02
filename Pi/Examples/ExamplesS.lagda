\begin{code}[hide]
{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances --allow-unsolved-metas #-}
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
    c c₁ c₂ c₃ c₄ : A Pi.⟷₁ B
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
infixr 30 _⟷₂_
infixr 60 _■_ 
infixr 70 _⊡_

data _⟷₂_ : {X : U} {Y : U} → X ⟷₁ Y → X ⟷₁ Y → Set where
\end{code}

\newcommand{\leveltwoblockone}{%
\begin{code}
  assoc◎l : c₁ ◎ (c₂ ◎ c₃) ⟷₂ (c₁ ◎ c₂) ◎ c₃
  assoc◎r : (c₁ ◎ c₂) ◎ c₃ ⟷₂ c₁ ◎ (c₂ ◎ c₃)
  idl◎l   : (id⟷₁ ◎ c) ⟷₂ c
  idl◎r   : c ⟷₂ id⟷₁ ◎ c
  idr◎r   : c ⟷₂ (c ◎ id⟷₁)
  linv◎l  : (c ◎ !⟷₁ c) ⟷₂ id⟷₁
  linv◎r  : id⟷₁ ⟷₂ (c ◎ !⟷₁ c)
  id⟷₂    : c ⟷₂ c
  _⊡_     : (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ◎ c₂) ⟷₂ (c₃ ◎ c₄)
  hexagonl₊l : (assocl₊ ◎ swap₊) ◎ assocl₊ ⟷₂ ((id⟷₁ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷₁)
  _■_  : (c₁ ⟷₂ c₂) → (c₂ ⟷₂ c₃) → (c₁ ⟷₂ c₃)
\end{code}}

\begin{code}[hide]
p₁ p₂ : A + (B + C) Pi.⟷₁ C + (B + A)
p₁ = assocl₊ ◎ swap₊ ◎ (id⟷₁ ⊕ swap₊)
p₂ = (id⟷₁ ⊕ swap₊) ◎ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊ ◎ (id⟷₁ ⊕ swap₊)
\end{code}

\newcommand{\leveltwoexample}{%
\begin{code}
p₁₂ : p₁ ⟷₂ p₂
p₁₂ = assoc◎l
    ■ ((idr◎r ■ (id⟷₂ ⊡ linv◎r) ■ assoc◎l ■ (hexagonl₊l ⊡ id⟷₂))
      ⊡ (idl◎r ■ (linv◎r ⊡ id⟷₂)))
    ■ ((id⟷₂ ⊡ (linv◎l ⊡ id⟷₂)) ■ (id⟷₂ ⊡ idl◎l))
    ■ assoc◎r ■ assoc◎r ■ assoc◎r
\end{code}}