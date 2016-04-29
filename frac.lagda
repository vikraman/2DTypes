\documentclass{article}
\usepackage{agda}
\usepackage[utf8x]{inputenc}
\usepackage{amsthm}
\usepackage{fullpage}
\usepackage{bbold}
\usepackage{url}
\usepackage{xcolor}
\usepackage{amssymb}
\usepackage{multicol}
\usepackage{proof}
\usepackage{amstext}
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{stmaryrd}
\usepackage{mathrsfs}

\newcommand{\alt}{~|~}
\newcommand{\inl}[1]{\textsf{inl}(#1)}
\newcommand{\inr}[1]{\textsf{inr}(#1)}
\newcommand{\zt}{\mathbb{0}}
\newcommand{\ot}{\mathbb{1}}
\newcommand{\G}{\mathcal{G}}
\newcommand{\Z}{\mathbb{Z}}
\newcommand{\Zn}{\mathbb{Z}_n}
\newcommand{\Zvn}{\mathbb{Z}^v_n}
\newcommand{\cycle}{\textsf{cycle}}
\newcommand{\twod}{\mathbb{T}}
\newcommand{\fract}[2]{#1/#2}
%% \newcommand{\mystrut}{\rule[-0.01\baselineskip]{0pt}{2.2\baselineskip}}
\newcommand{\fv}[2]{\fcolorbox{black}{white}{\strut $#1$}\fcolorbox{black}{gray!20}{$\strut #2$}}
\newcommand{\pt}[2]{\bullet[#1,#2]}
\newcommand{\refl}{\AgdaInductiveConstructor{refl}}

\theoremstyle{remark}
\newtheorem{definition}{Definition}
\newtheorem{example}{Example}

\renewcommand{\AgdaCodeStyle}{\small}
%% shorten the longarrow
\DeclareUnicodeCharacter{10231}{\ensuremath{\leftrightarrow}}
\DeclareUnicodeCharacter{9678}{$\circledcirc$}
\DeclareUnicodeCharacter{964}{$\tau$}
\DeclareUnicodeCharacter{945}{$\alpha$}
\DeclareUnicodeCharacter{7522}{${}_i$}
\DeclareUnicodeCharacter{8759}{$::$}
\DeclareUnicodeCharacter{737}{${}^{l}$}
\DeclareUnicodeCharacter{931}{$\Sigma$}
\DeclareUnicodeCharacter{8718}{$\qed$}

\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module frac where
open import Level renaming (zero to lzero; suc to lsuc) 
open import Algebra
open import Algebra.Structures
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Nat.Properties
open import Data.Fin using (Fin; zero; suc; inject+; raise; inject≤; toℕ; fromℕ)
  renaming (_+_ to _F+_)
open import Data.Fin.Properties
open import Data.Sum hiding (map)
open import Data.Bool
open import Data.Product hiding (map)
open import Data.Vec
open import Data.Nat hiding (_⊔_)
open import Data.Integer using (+_) 
open import Rational+ renaming (_+_ to _ℚ+_; _*_ to _ℚ*_)
  hiding (_≤_)
import Relation.Binary.PropositionalEquality as P
open import Categories.Category
open import Categories.Groupoid
open import Relation.Binary.Core using (Rel; IsEquivalence)

open import Level
open import Categories.Category 
import Categories.Morphisms
open import Relation.Binary
  using (Rel; IsEquivalence; module IsEquivalence; Reflexive; Symmetric; Transitive)
  renaming (_⇒_ to _⊆_)
open import Function using (flip)
open import Categories.Support.PropositionalEquality
open import Categories.Support.Equivalence
open import Categories.Support.EqReasoning
open import Data.Product
open import Categories.Groupoid
\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\title{Action Groupoids and Fractional Types}
\author{Everyone}
\begin{document}
\maketitle 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Background}
 
Our starting point is $\Pi$:
\begin{itemize}

\item We have finite types $\zt$, $\ot$, $\tau_1\oplus\tau_2$, and
$\tau_1\otimes\tau_2$. 

{\footnotesize{
\smallskip
\begin{code} 
data U : Set where
  ZERO   : U
  ONE    : U
  PLUS   : U → U → U
  TIMES  : U → U → U
\end{code}
}}

\item A type $\tau$ has points in $\llbracket \tau \rrbracket$:

{\footnotesize{
\smallskip
\begin{code} 
⟦_⟧ : U → Set
⟦ ZERO ⟧         = ⊥ 
⟦ ONE ⟧          = ⊤
⟦ PLUS t₁ t₂ ⟧   = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧  = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
\end{code}
}}

\item A type $\tau$ has a cardinality $|\tau|$ which just counts the points:

{\footnotesize{
\smallskip
\begin{code} 
∣_∣ : U → ℕ
∣ ZERO ∣         = 0
∣ ONE ∣          = 1
∣ PLUS t₁ t₂ ∣   = ∣ t₁ ∣ + ∣ t₂ ∣
∣ TIMES t₁ t₂ ∣  = ∣ t₁ ∣ * ∣ t₂ ∣
\end{code}
}}

\item We have combinators $c : \tau_1\leftrightarrow\tau_2$ between
  the types which witness type isomorphisms and which correspond to
  the axioms of commutative rigs. Combinators are also a
  representation of permutations and they preserve the size of types.

\item For $c_1, c_2 : \tau_1\leftrightarrow\tau_2$, we have level-2
 combinators $\alpha : c_1 \Leftrightarrow c_2$ which are (quite
 messy) equivalences of isomorphisms, and which happen to correspond
 to the coherence conditions for rig groupoids.

\end{itemize}

\AgdaHide{
\begin{code}
infix  30 _⟷_
infixr 50 _◎_

data _⟷_ : U → U → Set where
  unite₊l : {t : U} → PLUS ZERO t ⟷ t
  uniti₊l : {t : U} → t ⟷ PLUS ZERO t
  unite₊r : {t : U} → PLUS t ZERO ⟷ t
  uniti₊r : {t : U} → t ⟷ PLUS t ZERO
  swap₊   : {t₁ t₂ : U} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
  assocl₊ : {t₁ t₂ t₃ : U} → PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
  assocr₊ : {t₁ t₂ t₃ : U} → PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
  unite⋆l  : {t : U} → TIMES ONE t ⟷ t
  uniti⋆l  : {t : U} → t ⟷ TIMES ONE t
  unite⋆r : {t : U} → TIMES t ONE ⟷ t
  uniti⋆r : {t : U} → t ⟷ TIMES t ONE
  swap⋆   : {t₁ t₂ : U} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
  assocl⋆ : {t₁ t₂ t₃ : U} → TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
  assocr⋆ : {t₁ t₂ t₃ : U} → TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
  absorbr : {t : U} → TIMES ZERO t ⟷ ZERO
  absorbl : {t : U} → TIMES t ZERO ⟷ ZERO
  factorzr : {t : U} → ZERO ⟷ TIMES t ZERO
  factorzl : {t : U} → ZERO ⟷ TIMES ZERO t
  dist    : {t₁ t₂ t₃ : U} → 
            TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)
  factor  : {t₁ t₂ t₃ : U} → 
            PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
  distl   : {t₁ t₂ t₃ : U } →
            TIMES t₁ (PLUS t₂ t₃) ⟷ PLUS (TIMES t₁ t₂) (TIMES t₁ t₃)
  factorl : {t₁ t₂ t₃ : U } →
            PLUS (TIMES t₁ t₂) (TIMES t₁ t₃) ⟷ TIMES t₁ (PLUS t₂ t₃)
  id⟷    : {t : U} → t ⟷ t
  _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : U} → 
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : U} → 
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)

! : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
! unite₊l   = uniti₊l
! uniti₊l   = unite₊l
! unite₊r   = uniti₊r
! uniti₊r   = unite₊r
! swap₊     = swap₊
! assocl₊   = assocr₊
! assocr₊   = assocl₊
! unite⋆l   = uniti⋆l
! uniti⋆l   = unite⋆l
! unite⋆r   = uniti⋆r
! uniti⋆r   = unite⋆r
! swap⋆     = swap⋆
! assocl⋆   = assocr⋆
! assocr⋆   = assocl⋆
! absorbl   = factorzr
! absorbr   = factorzl
! factorzl  = absorbr
! factorzr  = absorbl
! dist      = factor 
! factor    = dist
! distl     = factorl
! factorl   = distl
! id⟷       = id⟷
! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁ 
! (c₁ ⊕ c₂) = (! c₁) ⊕ (! c₂)
! (c₁ ⊗ c₂) = (! c₁) ⊗ (! c₂)

infix  30 _⇔_

data _⇔_ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
  assoc◎l : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} →
          (c₁ ◎ (c₂ ◎ c₃)) ⇔ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
          ((c₁ ◎ c₂) ◎ c₃) ⇔ (c₁ ◎ (c₂ ◎ c₃))
  assocl⊕l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊) ⇔ (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃))
  assocl⊕r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃)) ⇔ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊)
  assocl⊗l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          ((c₁ ⊗ (c₂ ⊗ c₃)) ◎ assocl⋆) ⇔ (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃))
  assocl⊗r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (assocl⋆ ◎ ((c₁ ⊗ c₂) ⊗ c₃)) ⇔ ((c₁ ⊗ (c₂ ⊗ c₃)) ◎ assocl⋆)
  assocr⊕r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊) ⇔ (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃)))
  assocr⊗l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
           (assocr⋆ ◎ (c₁ ⊗ (c₂ ⊗ c₃))) ⇔ (((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆)
  assocr⊗r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
          (((c₁ ⊗ c₂) ⊗ c₃) ◎ assocr⋆) ⇔ (assocr⋆ ◎ (c₁ ⊗ (c₂ ⊗ c₃)))
  assocr⊕l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₅ ⟷ t₆} → 
           (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃))) ⇔ (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊)
  dist⇔l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
      ((a ⊕ b) ⊗ c) ◎ dist ⇔ dist ◎ ((a ⊗ c) ⊕ (b ⊗ c))
  dist⇔r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
      dist ◎ ((a ⊗ c) ⊕ (b ⊗ c)) ⇔ ((a ⊕ b) ⊗ c) ◎ dist
  distl⇔l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
      (a ⊗ (b ⊕ c)) ◎ distl ⇔ distl ◎ ((a ⊗ b) ⊕ (a ⊗ c))
  distl⇔r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
      distl ◎ ((a ⊗ b) ⊕ (a ⊗ c)) ⇔ (a ⊗ (b ⊕ c)) ◎ distl
  factor⇔l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
       ((a ⊗ c) ⊕ (b ⊗ c)) ◎ factor ⇔ factor ◎ ((a ⊕ b) ⊗ c)
  factor⇔r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
       factor ◎ ((a ⊕ b) ⊗ c) ⇔ ((a ⊗ c) ⊕ (b ⊗ c)) ◎ factor
  factorl⇔l : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
       ((a ⊗ b) ⊕ (a ⊗ c)) ◎ factorl ⇔ factorl ◎ (a ⊗ (b ⊕ c))
  factorl⇔r : {t₁ t₂ t₃ t₄ t₅ t₆ : U} 
          {a : t₁ ⟷ t₂} {b : t₃ ⟷ t₄} {c : t₅ ⟷ t₆} →
       factorl ◎ (a ⊗ (b ⊕ c)) ⇔ ((a ⊗ b) ⊕ (a ⊗ c)) ◎ factorl
  idl◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (id⟷ ◎ c) ⇔ c
  idl◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ id⟷ ◎ c
  idr◎l   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ id⟷) ⇔ c
  idr◎r   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ (c ◎ id⟷) 
  linv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ ! c) ⇔ id⟷
  linv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (c ◎ ! c) 
  rinv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (! c ◎ c) ⇔ id⟷
  rinv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (! c ◎ c) 
  unite₊l⇔l : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (unite₊l ◎ c₂) ⇔ ((c₁ ⊕ c₂) ◎ unite₊l)
  unite₊l⇔r : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          ((c₁ ⊕ c₂) ◎ unite₊l) ⇔ (unite₊l ◎ c₂)
  uniti₊l⇔l : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (uniti₊l ◎ (c₁ ⊕ c₂)) ⇔ (c₂ ◎ uniti₊l)
  uniti₊l⇔r : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (c₂ ◎ uniti₊l) ⇔ (uniti₊l ◎ (c₁ ⊕ c₂))
  unite₊r⇔l : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (unite₊r ◎ c₂) ⇔ ((c₂ ⊕ c₁) ◎ unite₊r)
  unite₊r⇔r : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          ((c₂ ⊕ c₁) ◎ unite₊r) ⇔ (unite₊r ◎ c₂)
  uniti₊r⇔l : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (uniti₊r ◎ (c₂ ⊕ c₁)) ⇔ (c₂ ◎ uniti₊r)
  uniti₊r⇔r : {t₁ t₂ : U} {c₁ : ZERO ⟷ ZERO} {c₂ : t₁ ⟷ t₂} → 
          (c₂ ◎ uniti₊r) ⇔ (uniti₊r ◎ (c₂ ⊕ c₁))
  swapl₊⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
          (swap₊ ◎ (c₁ ⊕ c₂)) ⇔ ((c₂ ⊕ c₁) ◎ swap₊)
  swapr₊⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
          ((c₂ ⊕ c₁) ◎ swap₊) ⇔ (swap₊ ◎ (c₁ ⊕ c₂))
  unitel⋆⇔l : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (unite⋆l ◎ c₂) ⇔ ((c₁ ⊗ c₂) ◎ unite⋆l)
  uniter⋆⇔l : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          ((c₁ ⊗ c₂) ◎ unite⋆l) ⇔ (unite⋆l ◎ c₂)
  unitil⋆⇔l : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (uniti⋆l ◎ (c₁ ⊗ c₂)) ⇔ (c₂ ◎ uniti⋆l)
  unitir⋆⇔l : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (c₂ ◎ uniti⋆l) ⇔ (uniti⋆l ◎ (c₁ ⊗ c₂))
  unitel⋆⇔r : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (unite⋆r ◎ c₂) ⇔ ((c₂ ⊗ c₁) ◎ unite⋆r)
  uniter⋆⇔r : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          ((c₂ ⊗ c₁) ◎ unite⋆r) ⇔ (unite⋆r ◎ c₂)
  unitil⋆⇔r : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (uniti⋆r ◎ (c₂ ⊗ c₁)) ⇔ (c₂ ◎ uniti⋆r)
  unitir⋆⇔r : {t₁ t₂ : U} {c₁ : ONE ⟷ ONE} {c₂ : t₁ ⟷ t₂} → 
          (c₂ ◎ uniti⋆r) ⇔ (uniti⋆r ◎ (c₂ ⊗ c₁))
  swapl⋆⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
          (swap⋆ ◎ (c₁ ⊗ c₂)) ⇔ ((c₂ ⊗ c₁) ◎ swap⋆)
  swapr⋆⇔ : {t₁ t₂ t₃ t₄ : U} {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} → 
          ((c₂ ⊗ c₁) ◎ swap⋆) ⇔ (swap⋆ ◎ (c₁ ⊗ c₂))
  id⇔     : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → c ⇔ c
  trans⇔  : {t₁ t₂ : U} {c₁ c₂ c₃ : t₁ ⟷ t₂} → 
         (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  _⊡_  : {t₁ t₂ t₃ : U} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₁ ⟷ t₂} {c₄ : t₂ ⟷ t₃} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ◎ c₂) ⇔ (c₃ ◎ c₄)
  resp⊕⇔  : {t₁ t₂ t₃ t₄ : U} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} → 
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊕ c₂) ⇔ (c₃ ⊕ c₄)
  resp⊗⇔  : {t₁ t₂ t₃ t₄ : U} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} → 
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊗ c₂) ⇔ (c₃ ⊗ c₄)
  -- below are the combinators added for the RigCategory structure
  id⟷⊕id⟷⇔ : {t₁ t₂ : U} → (id⟷ {t₁} ⊕ id⟷ {t₂}) ⇔ id⟷
  split⊕-id⟷ : {t₁ t₂ : U} → (id⟷ {PLUS t₁ t₂}) ⇔ (id⟷ ⊕ id⟷)
  hom⊕◎⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
        ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⇔ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
  hom◎⊕⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
         ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)) ⇔ ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄))
  id⟷⊗id⟷⇔ : {t₁ t₂ : U} → (id⟷ {t₁} ⊗ id⟷ {t₂}) ⇔ id⟷
  split⊗-id⟷ : {t₁ t₂ : U} → (id⟷ {TIMES t₁ t₂}) ⇔ (id⟷ ⊗ id⟷)
  hom⊗◎⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
        ((c₁ ◎ c₃) ⊗ (c₂ ◎ c₄)) ⇔ ((c₁ ⊗ c₂) ◎ (c₃ ⊗ c₄))
  hom◎⊗⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
         ((c₁ ⊗ c₂) ◎ (c₃ ⊗ c₄)) ⇔ ((c₁ ◎ c₃) ⊗ (c₂ ◎ c₄))
  -- associativity triangle
  triangle⊕l : {t₁ t₂ : U} →
    (unite₊r {t₁} ⊕ id⟷ {t₂}) ⇔ assocr₊ ◎ (id⟷ ⊕ unite₊l)
  triangle⊕r : {t₁ t₂ : U} →
    assocr₊ ◎ (id⟷ {t₁} ⊕ unite₊l {t₂}) ⇔ (unite₊r ⊕ id⟷)
  triangle⊗l : {t₁ t₂ : U} →
    ((unite⋆r {t₁}) ⊗ id⟷ {t₂}) ⇔ assocr⋆ ◎ (id⟷ ⊗ unite⋆l)
  triangle⊗r : {t₁ t₂ : U} →
    (assocr⋆ ◎ (id⟷ {t₁} ⊗ unite⋆l {t₂})) ⇔ (unite⋆r ⊗ id⟷)
  pentagon⊕l : {t₁ t₂ t₃ t₄ : U} →
    assocr₊ ◎ (assocr₊ {t₁} {t₂} {PLUS t₃ t₄}) ⇔
    ((assocr₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ assocr₊)
  pentagon⊕r : {t₁ t₂ t₃ t₄ : U} →
    ((assocr₊ {t₁} {t₂} {t₃} ⊕ id⟷ {t₄}) ◎ assocr₊) ◎ (id⟷ ⊕ assocr₊) ⇔
    assocr₊ ◎ assocr₊
  pentagon⊗l : {t₁ t₂ t₃ t₄ : U} →
    assocr⋆ ◎ (assocr⋆ {t₁} {t₂} {TIMES t₃ t₄}) ⇔
    ((assocr⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ assocr⋆)
  pentagon⊗r : {t₁ t₂ t₃ t₄ : U} →
    ((assocr⋆ {t₁} {t₂} {t₃} ⊗ id⟷ {t₄}) ◎ assocr⋆) ◎ (id⟷ ⊗ assocr⋆) ⇔ 
    assocr⋆ ◎ assocr⋆
  -- from the braiding
  -- unit coherence
  unite₊l-coh-l : {t₁ : U} → unite₊l {t₁} ⇔ swap₊ ◎ unite₊r
  unite₊l-coh-r : {t₁ : U} → swap₊ ◎ unite₊r ⇔ unite₊l {t₁}
  unite⋆l-coh-l : {t₁ : U} → unite⋆l {t₁} ⇔ swap⋆ ◎ unite⋆r
  unite⋆l-coh-r : {t₁ : U} → swap⋆ ◎ unite⋆r ⇔ unite⋆l {t₁}
  hexagonr⊕l : {t₁ t₂ t₃ : U} →
    (assocr₊ ◎ swap₊) ◎ assocr₊ {t₁} {t₂} {t₃} ⇔
    ((swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊)
  hexagonr⊕r : {t₁ t₂ t₃ : U} →
    ((swap₊ ⊕ id⟷) ◎ assocr₊) ◎ (id⟷ ⊕ swap₊) ⇔
    (assocr₊ ◎ swap₊) ◎ assocr₊ {t₁} {t₂} {t₃}
  hexagonl⊕l : {t₁ t₂ t₃ : U} →
    (assocl₊ ◎ swap₊) ◎ assocl₊ {t₁} {t₂} {t₃} ⇔
    ((id⟷ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷)
  hexagonl⊕r : {t₁ t₂ t₃ : U} →
    ((id⟷ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷) ⇔
    (assocl₊ ◎ swap₊) ◎ assocl₊ {t₁} {t₂} {t₃}
  hexagonr⊗l : {t₁ t₂ t₃ : U} →
    (assocr⋆ ◎ swap⋆) ◎ assocr⋆ {t₁} {t₂} {t₃} ⇔
    ((swap⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ swap⋆)
  hexagonr⊗r : {t₁ t₂ t₃ : U} →
    ((swap⋆ ⊗ id⟷) ◎ assocr⋆) ◎ (id⟷ ⊗ swap⋆) ⇔
    (assocr⋆ ◎ swap⋆) ◎ assocr⋆ {t₁} {t₂} {t₃}
  hexagonl⊗l : {t₁ t₂ t₃ : U} →
    (assocl⋆ ◎ swap⋆) ◎ assocl⋆ {t₁} {t₂} {t₃} ⇔
    ((id⟷ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷)
  hexagonl⊗r : {t₁ t₂ t₃ : U} →
    ((id⟷ ⊗ swap⋆) ◎ assocl⋆) ◎ (swap⋆ ⊗ id⟷) ⇔
    (assocl⋆ ◎ swap⋆) ◎ assocl⋆ {t₁} {t₂} {t₃}
  absorbl⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    (c₁ ⊗ id⟷ {ZERO}) ◎ absorbl ⇔ absorbl ◎ id⟷ {ZERO}
  absorbl⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    absorbl ◎ id⟷ {ZERO} ⇔ (c₁ ⊗ id⟷ {ZERO}) ◎ absorbl
  absorbr⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    (id⟷ {ZERO} ⊗ c₁) ◎ absorbr ⇔ absorbr ◎ id⟷ {ZERO}
  absorbr⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    absorbr ◎ id⟷ {ZERO} ⇔ (id⟷ {ZERO} ⊗ c₁) ◎ absorbr
  factorzl⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    id⟷ ◎ factorzl ⇔ factorzl ◎ (id⟷ ⊗ c₁)
  factorzl⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    factorzl ◎ (id⟷ {ZERO} ⊗ c₁) ⇔ id⟷ {ZERO} ◎ factorzl
  factorzr⇔l : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    id⟷ ◎ factorzr ⇔ factorzr ◎ (c₁ ⊗ id⟷)
  factorzr⇔r : {t₁ t₂ : U} {c₁ : t₁ ⟷ t₂} →
    factorzr ◎ (c₁ ⊗ id⟷) ⇔ id⟷ ◎ factorzr
  -- from the coherence conditions of RigCategory
  swap₊distl⇔l : {t₁ t₂ t₃ : U} →
    (id⟷ {t₁} ⊗ swap₊ {t₂} {t₃}) ◎ distl ⇔ distl ◎ swap₊
  swap₊distl⇔r : {t₁ t₂ t₃ : U} →
    distl ◎ swap₊ ⇔ (id⟷ {t₁} ⊗ swap₊ {t₂} {t₃}) ◎ distl
  dist-swap⋆⇔l : {t₁ t₂ t₃ : U} →
    dist {t₁} {t₂} {t₃} ◎ (swap⋆ ⊕ swap⋆) ⇔ swap⋆ ◎ distl
  dist-swap⋆⇔r : {t₁ t₂ t₃ : U} →
    swap⋆ ◎ distl {t₁} {t₂} {t₃} ⇔ dist ◎ (swap⋆ ⊕ swap⋆)
  assocl₊-dist-dist⇔l : {t₁ t₂ t₃ t₄ : U} →
    ((assocl₊ {t₁} {t₂} {t₃} ⊗ id⟷ {t₄}) ◎ dist) ◎ (dist ⊕ id⟷) ⇔
    (dist ◎ (id⟷ ⊕ dist)) ◎ assocl₊
  assocl₊-dist-dist⇔r : {t₁ t₂ t₃ t₄ : U} →
    (dist {t₁} ◎ (id⟷ ⊕ dist {t₂} {t₃} {t₄})) ◎ assocl₊ ⇔
    ((assocl₊ ⊗ id⟷) ◎ dist) ◎ (dist ⊕ id⟷)
  assocl⋆-distl⇔l : {t₁ t₂ t₃ t₄ : U} →
    assocl⋆ {t₁} {t₂} ◎ distl {TIMES t₁ t₂} {t₃} {t₄} ⇔
    ((id⟷ ⊗ distl) ◎ distl) ◎ (assocl⋆ ⊕ assocl⋆)
  assocl⋆-distl⇔r : {t₁ t₂ t₃ t₄ : U} →
    ((id⟷ ⊗ distl) ◎ distl) ◎ (assocl⋆ ⊕ assocl⋆) ⇔
    assocl⋆ {t₁} {t₂} ◎ distl {TIMES t₁ t₂} {t₃} {t₄}  
  absorbr0-absorbl0⇔ : absorbr {ZERO} ⇔ absorbl {ZERO}
  absorbl0-absorbr0⇔ : absorbl {ZERO} ⇔ absorbr {ZERO}
  absorbr⇔distl-absorb-unite : {t₁ t₂ : U} →
    absorbr ⇔ (distl {t₂ = t₁} {t₂} ◎ (absorbr ⊕ absorbr)) ◎ unite₊l
  distl-absorb-unite⇔absorbr : {t₁ t₂ : U} →
    (distl {t₂ = t₁} {t₂} ◎ (absorbr ⊕ absorbr)) ◎ unite₊l ⇔ absorbr
  unite⋆r0-absorbr1⇔ : unite⋆r ⇔ absorbr
  absorbr1-unite⋆r-⇔ : absorbr ⇔ unite⋆r
  absorbl≡swap⋆◎absorbr : {t₁ : U} → absorbl {t₁} ⇔ swap⋆ ◎ absorbr
  swap⋆◎absorbr≡absorbl : {t₁ : U} → swap⋆ ◎ absorbr ⇔ absorbl {t₁}
  absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr : {t₁ t₂ : U} →
    absorbr ⇔ (assocl⋆ {ZERO} {t₁} {t₂} ◎ (absorbr ⊗ id⟷)) ◎ absorbr
  [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⇔absorbr : {t₁ t₂ : U} →
    (assocl⋆ {ZERO} {t₁} {t₂} ◎ (absorbr ⊗ id⟷)) ◎ absorbr ⇔ absorbr
  [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr : {t₁ t₂ : U} →
    (id⟷ ⊗ absorbr {t₂}) ◎ absorbl {t₁} ⇔
    (assocl⋆ ◎ (absorbl ⊗ id⟷)) ◎ absorbr
  assocl⋆◎[absorbl⊗id⟷]◎absorbr⇔[id⟷⊗absorbr]◎absorbl : {t₁ t₂ : U} →
    (assocl⋆ ◎ (absorbl ⊗ id⟷)) ◎ absorbr ⇔
    (id⟷ ⊗ absorbr {t₂}) ◎ absorbl {t₁}
  elim⊥-A[0⊕B]⇔l : {t₁ t₂ : U} →
     (id⟷ {t₁} ⊗ unite₊l {t₂}) ⇔
     (distl ◎ (absorbl ⊕ id⟷)) ◎ unite₊l
  elim⊥-A[0⊕B]⇔r : {t₁ t₂ : U} →
     (distl ◎ (absorbl ⊕ id⟷)) ◎ unite₊l ⇔ (id⟷ {t₁} ⊗ unite₊l {t₂})
  elim⊥-1[A⊕B]⇔l : {t₁ t₂ : U} →
    unite⋆l ⇔ 
    distl ◎ (unite⋆l {t₁} ⊕ unite⋆l {t₂})
  elim⊥-1[A⊕B]⇔r : {t₁ t₂ : U} →
    distl ◎ (unite⋆l {t₁} ⊕ unite⋆l {t₂}) ⇔ unite⋆l
  fully-distribute⇔l : {t₁ t₂ t₃ t₄ : U} → 
    (distl ◎ (dist {t₁} {t₂} {t₃} ⊕ dist {t₁} {t₂} {t₄})) ◎ assocl₊ ⇔
      ((((dist ◎ (distl ⊕ distl)) ◎ assocl₊) ◎ (assocr₊ ⊕ id⟷)) ◎
         ((id⟷ ⊕ swap₊) ⊕ id⟷)) ◎ (assocl₊ ⊕ id⟷)
  fully-distribute⇔r : {t₁ t₂ t₃ t₄ : U} →
    ((((dist ◎ (distl ⊕ distl)) ◎ assocl₊) ◎ (assocr₊ ⊕ id⟷)) ◎
       ((id⟷ ⊕ swap₊) ⊕ id⟷)) ◎ (assocl₊ ⊕ id⟷) ⇔
    (distl ◎ (dist {t₁} {t₂} {t₃} ⊕ dist {t₁} {t₂} {t₄})) ◎ assocl₊

2! : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
2! assoc◎l = assoc◎r
2! assoc◎r = assoc◎l
2! assocl⊕l = assocl⊕r
2! assocl⊕r = assocl⊕l
2! assocl⊗l = assocl⊗r
2! assocl⊗r = assocl⊗l
2! assocr⊕r = assocr⊕l
2! assocr⊕l = assocr⊕r
2! assocr⊗r = assocr⊗l
2! assocr⊗l = assocr⊗r
2! dist⇔l = dist⇔r
2! dist⇔r = dist⇔l
2! distl⇔l = distl⇔r
2! distl⇔r = distl⇔l
2! factor⇔l = factor⇔r
2! factor⇔r = factor⇔l
2! factorl⇔l = factorl⇔r
2! factorl⇔r = factorl⇔l
2! idl◎l = idl◎r
2! idl◎r = idl◎l
2! idr◎l = idr◎r
2! idr◎r = idr◎l
2! linv◎l = linv◎r
2! linv◎r = linv◎l
2! rinv◎l = rinv◎r
2! rinv◎r = rinv◎l
2! unite₊l⇔l = unite₊l⇔r
2! unite₊l⇔r = unite₊l⇔l
2! uniti₊l⇔l = uniti₊l⇔r
2! uniti₊l⇔r = uniti₊l⇔l
2! unite₊r⇔l = unite₊r⇔r
2! unite₊r⇔r = unite₊r⇔l
2! uniti₊r⇔l = uniti₊r⇔r
2! uniti₊r⇔r = uniti₊r⇔l
2! swapl₊⇔ = swapr₊⇔
2! swapr₊⇔ = swapl₊⇔
2! unitel⋆⇔l = uniter⋆⇔l
2! uniter⋆⇔l = unitel⋆⇔l
2! unitil⋆⇔l = unitir⋆⇔l
2! unitir⋆⇔l = unitil⋆⇔l
2! unitel⋆⇔r = uniter⋆⇔r
2! uniter⋆⇔r = unitel⋆⇔r
2! unitil⋆⇔r = unitir⋆⇔r
2! unitir⋆⇔r = unitil⋆⇔r
2! swapl⋆⇔ = swapr⋆⇔
2! swapr⋆⇔ = swapl⋆⇔
2! id⇔ = id⇔
2! (α ⊡ β) = (2! α) ⊡ (2! β)
2! (trans⇔ α β) = trans⇔ (2! β) (2! α)
2! (resp⊕⇔ α β) = resp⊕⇔ (2! α) (2! β)
2! (resp⊗⇔ α β) = resp⊗⇔ (2! α) (2! β)
2! id⟷⊕id⟷⇔ = split⊕-id⟷
2! split⊕-id⟷ = id⟷⊕id⟷⇔
2! hom⊕◎⇔ = hom◎⊕⇔
2! hom◎⊕⇔ = hom⊕◎⇔
2! id⟷⊗id⟷⇔ = split⊗-id⟷
2! split⊗-id⟷ = id⟷⊗id⟷⇔
2! hom⊗◎⇔ = hom◎⊗⇔
2! hom◎⊗⇔ = hom⊗◎⇔
2! triangle⊕l = triangle⊕r
2! triangle⊕r = triangle⊕l
2! triangle⊗l = triangle⊗r
2! triangle⊗r = triangle⊗l
2! pentagon⊕l = pentagon⊕r
2! pentagon⊕r = pentagon⊕l
2! pentagon⊗l = pentagon⊗r
2! pentagon⊗r = pentagon⊗l
2! unite₊l-coh-l = unite₊l-coh-r
2! unite₊l-coh-r = unite₊l-coh-l
2! unite⋆l-coh-l = unite⋆l-coh-r
2! unite⋆l-coh-r = unite⋆l-coh-l
2! hexagonr⊕l = hexagonr⊕r
2! hexagonr⊕r = hexagonr⊕l
2! hexagonl⊕l = hexagonl⊕r
2! hexagonl⊕r = hexagonl⊕l
2! hexagonr⊗l = hexagonr⊗r
2! hexagonr⊗r = hexagonr⊗l
2! hexagonl⊗l = hexagonl⊗r
2! hexagonl⊗r = hexagonl⊗l
2! absorbl⇔l = absorbl⇔r
2! absorbl⇔r = absorbl⇔l
2! absorbr⇔l = absorbr⇔r
2! absorbr⇔r = absorbr⇔l
2! factorzl⇔l = factorzl⇔r
2! factorzl⇔r = factorzl⇔l
2! factorzr⇔l = factorzr⇔r
2! factorzr⇔r = factorzr⇔l
2! swap₊distl⇔l = swap₊distl⇔r
2! swap₊distl⇔r = swap₊distl⇔l
2! dist-swap⋆⇔l = dist-swap⋆⇔r
2! dist-swap⋆⇔r = dist-swap⋆⇔l
2! assocl₊-dist-dist⇔l = assocl₊-dist-dist⇔r
2! assocl₊-dist-dist⇔r = assocl₊-dist-dist⇔l
2! assocl⋆-distl⇔l = assocl⋆-distl⇔r
2! assocl⋆-distl⇔r = assocl⋆-distl⇔l
2! absorbr0-absorbl0⇔ = absorbl0-absorbr0⇔
2! absorbl0-absorbr0⇔ = absorbr0-absorbl0⇔
2! absorbr⇔distl-absorb-unite = distl-absorb-unite⇔absorbr
2! distl-absorb-unite⇔absorbr = absorbr⇔distl-absorb-unite
2! unite⋆r0-absorbr1⇔ = absorbr1-unite⋆r-⇔
2! absorbr1-unite⋆r-⇔ = unite⋆r0-absorbr1⇔
2! absorbl≡swap⋆◎absorbr = swap⋆◎absorbr≡absorbl
2! swap⋆◎absorbr≡absorbl = absorbl≡swap⋆◎absorbr
2! absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr = 
    [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⇔absorbr
2!  [assocl⋆◎[absorbr⊗id⟷]]◎absorbr⇔absorbr = 
    absorbr⇔[assocl⋆◎[absorbr⊗id⟷]]◎absorbr
2! [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr =
    assocl⋆◎[absorbl⊗id⟷]◎absorbr⇔[id⟷⊗absorbr]◎absorbl
2! assocl⋆◎[absorbl⊗id⟷]◎absorbr⇔[id⟷⊗absorbr]◎absorbl =
    [id⟷⊗absorbr]◎absorbl⇔assocl⋆◎[absorbl⊗id⟷]◎absorbr
2! elim⊥-A[0⊕B]⇔l = elim⊥-A[0⊕B]⇔r
2! elim⊥-A[0⊕B]⇔r = elim⊥-A[0⊕B]⇔l
2! elim⊥-1[A⊕B]⇔l = elim⊥-1[A⊕B]⇔r
2! elim⊥-1[A⊕B]⇔r = elim⊥-1[A⊕B]⇔l
2! fully-distribute⇔l = fully-distribute⇔r
2! fully-distribute⇔r = fully-distribute⇔l

-- 0-dimensional evaluator

ap : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧
ap unite₊l (inj₁ ())
ap unite₊l (inj₂ v) = v
ap uniti₊l v = inj₂ v
ap unite₊r (inj₁ x) = x
ap unite₊r (inj₂ ())
ap uniti₊r v = inj₁ v
ap swap₊ (inj₁ v) = inj₂ v
ap swap₊ (inj₂ v) = inj₁ v
ap assocl₊ (inj₁ v) = inj₁ (inj₁ v)
ap assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
ap assocl₊ (inj₂ (inj₂ v)) = inj₂ v
ap assocr₊ (inj₁ (inj₁ v)) = inj₁ v
ap assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
ap assocr₊ (inj₂ v) = inj₂ (inj₂ v)
ap unite⋆l (tt , v) = v
ap uniti⋆l v = (tt , v)
ap unite⋆r (v , tt) = v
ap uniti⋆r v = v , tt
ap swap⋆ (v₁ , v₂) = (v₂ , v₁)
ap assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
ap assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
ap absorbr (x , _) = x
ap absorbl (_ , y) = y
ap factorzl ()
ap factorzr ()
ap dist (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
ap dist (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
ap factor (inj₁ (v₁ , v₃)) = (inj₁ v₁ , v₃)
ap factor (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)
ap distl (v , inj₁ x) = inj₁ (v , x)
ap distl (v , inj₂ y) = inj₂ (v , y)
ap factorl (inj₁ (x , y)) = x , inj₁ y
ap factorl (inj₂ (x , y)) = x , inj₂ y
ap id⟷ v = v
ap (c₁ ◎ c₂) v = ap c₂ (ap c₁ v)
ap (c₁ ⊕ c₂) (inj₁ v) = inj₁ (ap c₁ v)
ap (c₁ ⊕ c₂) (inj₂ v) = inj₂ (ap c₂ v)
ap (c₁ ⊗ c₂) (v₁ , v₂) = (ap c₁ v₁ , ap c₂ v₂)

-- useful to have the backwards ap too

ap! : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₂ ⟧ → ⟦ t₁ ⟧
ap! unite₊l x = inj₂ x
ap! uniti₊l (inj₁ ())
ap! uniti₊l (inj₂ y) = y
ap! unite₊r v = inj₁ v
ap! uniti₊r (inj₁ x) = x
ap! uniti₊r (inj₂ ())
ap! swap₊ (inj₁ x) = inj₂ x
ap! swap₊ (inj₂ y) = inj₁ y
ap! assocl₊ (inj₁ (inj₁ x)) = inj₁ x
ap! assocl₊ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
ap! assocl₊ (inj₂ y) = inj₂ (inj₂ y)
ap! assocr₊ (inj₁ x) = inj₁ (inj₁ x)
ap! assocr₊ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
ap! assocr₊ (inj₂ (inj₂ y)) = inj₂ y
ap! unite⋆l x = tt , x
ap! uniti⋆l (tt , x) = x
ap! unite⋆r v = v , tt
ap! uniti⋆r (v , tt) = v
ap! swap⋆ (x , y) = y , x
ap! assocl⋆ ((x , y) , z) = x , y , z
ap! assocr⋆ (x , y , z) = (x , y) , z
ap! absorbr ()
ap! absorbl ()
ap! factorzr (_ , x) = x
ap! factorzl (x , _) = x
ap! dist (inj₁ (x , y)) = inj₁ x , y
ap! dist (inj₂ (x , y)) = inj₂ x , y
ap! factor (inj₁ x , z) = inj₁ (x , z)
ap! factor (inj₂ y , z) = inj₂ (y , z)
ap! distl (inj₁ (x , y)) = x , inj₁ y
ap! distl (inj₂ (x , y)) = x , inj₂ y
ap! factorl (v , inj₁ x) = inj₁ (v , x)
ap! factorl (v , inj₂ y) = inj₂ (v , y)
ap! id⟷ x = x
ap! (c₀ ◎ c₁) x = ap! c₀ (ap! c₁ x)
ap! (c₀ ⊕ c₁) (inj₁ x) = inj₁ (ap! c₀ x)
ap! (c₀ ⊕ c₁) (inj₂ y) = inj₂ (ap! c₁ y)
ap! (c₀ ⊗ c₁) (x , y) = ap! c₀ x , ap! c₁ y

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Permutations are Types}

\begin{code}
-- Permutation to groupoid

repeat : {A : Set} → (k : ℕ) → (A → A) → A → A
repeat 0 f x = x
repeat (suc k) f x = repeat k f (f x)

repeat+ : {A : Set} {x : A} {f : A → A} →
          (k₁ k₂ : ℕ) → repeat k₂ f (repeat k₁ f x) P.≡ repeat (k₁ + k₂) f x
repeat+ ℕ.zero k₂ = P.refl
repeat+ {x = x} {f = f} (ℕ.suc k₁) k₂ = repeat+ {x = f x} k₁ k₂ 

repeat∘ : {A : Set} {x y z : A} {k₁ k₂ : ℕ} {f : A → A} →
          repeat k₁ f x P.≡ y → repeat k₂ f y P.≡ z → repeat (k₁ + k₂) f x P.≡ z
repeat∘ {z = z} {k₁ = k₁} {k₂ = k₂} {f = f} a₁ a₂ =
  P.trans (P.sym (repeat+ k₁ k₂)) (P.subst (λ h → repeat k₂ f h P.≡ z) (P.sym a₁) a₂) 

p⇒C : {τ : U} (p : τ ⟷ τ) → Category lzero lzero lzero
p⇒C {τ} p = record {
     Obj = ⟦ τ ⟧ 
   ; _⇒_ = λ v₁ v₂ → Σ[ k ∈ ℕ ] repeat k (ap p) v₁ P.≡ v₂ 
   ; _≡_ = λ _ _ → ⊤
   ; id = (0 , P.refl) 
   ; _∘_ = λ { {v₁} {v₂} {v₃} (k₂ , a₂) (k₁ , a₁) →
             (k₁ + k₂ , repeat∘ {⟦ τ ⟧} {v₁} {v₂} {v₃} {k₁} {k₂} {ap p} a₁ a₂)} 
   ; assoc = tt 
   ; identityˡ = tt 
   ; identityʳ = tt 
   ; equiv = record { refl = tt; sym = λ _ → tt; trans = λ _ _ → tt } 
   ; ∘-resp-≡ = λ _ _ → tt 
   }

p⇒G : {τ : U} (p : τ ⟷ τ) → Groupoid (p⇒C p)
p⇒G {τ} p = record
  { _⁻¹ = λ { {v₁} {v₂} (k , a) → (k , {!!})} -- have a  : repeat k (ap p) v₁ = v₂; want: repeat k (ap p) v₂ = v₁
  ; iso = record { isoˡ = {!!}; isoʳ = {!!}}
  }

-- The other way of getting a groupoid from a permutation

compose : {τ : U} → (k : ℕ) → (p : τ ⟷ τ) → (τ ⟷ τ)
compose ℕ.zero p = id⟷
compose (ℕ.suc k) p = p ◎ compose k p 

compose+ : {τ : U} {p : τ ⟷ τ} →
         (k₁ k₂ : ℕ) → ((compose k₁ p) ◎ (compose k₂ p)) ⇔ compose (k₁ + k₂) p
compose+ ℕ.zero k₂ = idl◎l
compose+ (ℕ.suc k₁) k₂ = trans⇔ assoc◎r (id⇔ ⊡ (compose+ k₁ k₂))

-- Perm p is the singleton type that only contains p. 

Perm : {τ : U} → (p : τ ⟷ τ) → Set
Perm {τ} p = Σ[ p' ∈ (τ ⟷ τ) ] (p' ⇔ p)

singleton : {τ : U} → (p : τ ⟷ τ) → Perm p
singleton p = (p , id⇔)

p/⇒C : {τ : U} (p : τ ⟷ τ) → Category lzero lzero lzero
p/⇒C {τ} p = record {
     Obj = ⊤
   ; _⇒_ = λ _ _ → Σ[ k ∈ ℕ ] (Perm (compose k p)) 
   ; _≡_ = λ { (k₁ , (p₁ , α₁)) (k₂ , (p₂ , α₂)) → p₁ ⇔ p₂} 
   ; id = (0 , singleton id⟷) 
   ; _∘_ = λ { (k₂ , (p₂ , α₂)) (k₁ , (p₁ , α₁)) →
               (k₁ + k₂ ,  (p₁ ◎ p₂ , trans⇔ (α₁ ⊡ α₂) (compose+ k₁ k₂))) } 
   ; assoc = assoc◎l 
   ; identityˡ = idr◎l 
   ; identityʳ = idl◎l 
   ; equiv = record { refl = id⇔; sym = 2!; trans = trans⇔ }
   ; ∘-resp-≡ = λ f g → g ⊡ f 
   }

p/⇒G : {τ : U} (p : τ ⟷ τ) → Groupoid (p/⇒C p)
p/⇒G {τ} p = record
  { _⁻¹ = {!!}
  ; iso = record { isoˡ = {!!}; isoʳ = {!!}}
  }

\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\end{document}

we only care about left group actions; every type comes with an
enumeration (which is cyclic group); we have the group element that
says rotate 0 positions; another that says rotate $i$ positions
etc. So at the end we have a fucntion that takes $k$ and rotates $k$
times. Giving 0 is the identity and the number range from 0 to less
than the size of the type. 

0-skeleton: 3 points

  Focus   point   other-point


1-skeleton: one path skeleton

  Anchored-endpoint -------- loose-endpoint that can connect to point or other-point so this gives us 1/2

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Pointed Types and Path Skeletons}

\begin{itemize}

\item We introduce \emph{pointed types}. A pointed type $\pt{\tau}{v}$
  is a non-empty type $\tau$ along with one specific value $v : \tau$
  that is considered ``in focus.''  Examples:

{\footnotesize{
\begin{code}
-- record U• : Set where
--   constructor •[_,_]
--   field
--     carrier : U
--     •    : ⟦ carrier ⟧

-- pt₁ pt₂ pt₃ : U•
-- pt₁ = •[ PLUS ONE ONE , (inj₁ tt) ]
-- pt₂ = •[ PLUS ONE ONE , (inj₂ tt) ]
-- pt₃ = •[ TIMES ONE ONE , (tt , tt) ]
\end{code}
\smallskip

\AgdaHide{
\begin{code}
-- open U•
\end{code}
}}}

\item Of course we can never build a pointed type whose carrier is the
  empty type.

\item We will think of the special point in focus as the start point
of a path whose endpoint is unspecified. To that end, we introduce
\emph{path skeletons}. These are paths connecting the points
\emph{inside} the types and \emph{not} paths \emph{between} the types,
i.e., these are not type isomorphisms, permutations, equivalences,
etc. From any particular point, we can build the skeleton paths
starting at that point and ending at an arbitrary point within
\emph{any other} type.

\begin{code}
-- data _≈_ {t₁ t₂ : U} : (x : ⟦ t₁ ⟧) → (y : ⟦ t₂ ⟧) → Set where
--  eq : (x : ⟦ t₁ ⟧) (y : ⟦ t₂ ⟧) → x ≈ y

-- points→paths : (pt : U•) → {t : U} → (y : ⟦ t ⟧) → (• pt ≈ y)
-- points→paths •[ t , x ] y = eq x y

\end{code}

\item Now we introduce something interesting: a type built from a
set of points together with a family of skeleton paths.

\begin{code}
-- record FiniteGroupoid : Set where
--   field
--     S : U
--     G : Σ[ pt ∈ U• ] ((y : ⟦ S ⟧) → (• pt ≈ y))

-- -- Examples 1/2

-- 1/2 : FiniteGroupoid
-- 1/2 = record {
--         S = PLUS ONE ONE
--       ; G = (•[ ONE , tt ] , λ y → eq tt y)
--       }
                  

\end{code}



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{2D-types: Intuition}
 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Pointed Types} 
 
\begin{itemize}

\item All the combinators $c : \tau_1\leftrightarrow\tau_2$ can be
  lifted to pointed types. See Fig.~\ref{pointedcomb}. (Alternatively
  we can use eval and derive the lifted combinators as coherent
  actions. At this point we are not yet using the pointed
  combinators. We will see how things develop.)

\end{itemize}



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{2D-types}
 
\begin{itemize}
\item We generalize types in another way by adding another level; in
the next section we will combine the pointed types with the additional
level.

\item We generalize the syntax of types to include fractional types
  $\tau_1/\tau_2$. The idea will be that $\tau_1$ denotes a set $S$
  and $\tau_2$ denotes a group $\G$ and that $\fract{\tau_1}{\tau_2}$
  denotes the action groupoid $S \rtimes \G$.

\item We actually have two levels of types:
\[\begin{array}{rcl} 
\tau &::=& \zt \alt \ot \alt \tau_1\oplus\tau_2 \alt \tau_1\otimes\tau_2 \\
\twod &::=& \fract{\tau_1}{\tau_2} \alt \twod_1 \boxplus \twod_2
            \alt \twod_1 \boxtimes \twod_2  
\end{array}\]
The $\tau$ level describes plain sets. The $\twod$ level describes
``two-dimensional types'' which denote action groupoids. 

\item We will represent a cyclic group as a vector of values where the
group operation maps each value to the next and the last to the
first. We first define this vector of values as an enumeration, then
define action groupoids, and then our 2D types. This definition will
allow divisions by zero so we then move everything to pointed types.

\begin{code}
-- _enum×_ : {t₁ t₂ : U} →
--   Vec ⟦ t₁ ⟧ ∣ t₁ ∣ → Vec ⟦ t₂ ⟧ ∣ t₂ ∣ → Vec ⟦ TIMES t₁ t₂ ⟧ ∣ TIMES t₁ t₂ ∣ 
-- vs₁ enum× vs₂ = {!!} -- concat (map (λ v₁ → map (λ v₂ → (v₁ , v₂)) vs₂) vs₁)

-- enum : (t : U) → Vec ⟦ t ⟧ ∣ t ∣ 
-- enum ZERO = []
-- enum ONE = tt ∷ []
-- enum (PLUS t₁ t₂) = {!!} -- map inj₁ (enum t₁) ++ map inj₂ (enum t₂)
-- enum (TIMES t₁ t₂) = (enum t₁) enum× (enum t₂)

-- record Enum : Set where
--   constructor mkEnum
--   field
--     t : U
--     elems : Vec ⟦ t ⟧ ∣ t ∣ 

-- _Enum×_ : Enum → Enum → Enum
-- (mkEnum t₁ elems₁) Enum× (mkEnum t₂ elems₂) =
--   mkEnum (TIMES t₁ t₂) (elems₁ enum× elems₂)
        
-- postulate
--   mule : {A : Set} {n : ℕ} → (Vec A n) → (x y : A) → A
--   -- get index of x (must be there)
--   -- get index of y (must be there)
--   -- new index is x + y mod n
--   -- return elem at new index

--

-- record ActionGroupoid : Set₁ where
--   constructor _//_
--   field
--     S : Set
--     G : Enum

-- plus2 : ActionGroupoid → ActionGroupoid → ActionGroupoid
-- plus2 (S₁ // enum₁) (S₂ // enum₂) = 
--   ((S₁ × ⟦ Enum.t enum₂ ⟧) ⊎ (S₂ × ⟦ Enum.t enum₁ ⟧)) //
--   (enum₁ Enum× enum₂)

-- times2 : ActionGroupoid → ActionGroupoid → ActionGroupoid
-- times2 (S₁ // enum₁) (S₂ // enum₂) = (S₁ × S₂) // (enum₁ Enum× enum₂)

-- --

-- data 2D : Set where
--   LIFT    : (t : U) → 2D
--   RECIP   : (t : U) → 2D
--   PLUS2   : 2D → 2D → 2D
--   TIMES2  : 2D → 2D → 2D

-- 2⟦_⟧ : 2D → ActionGroupoid
-- 2⟦ LIFT t ⟧        = {!!}
-- 2⟦ RECIP t ⟧       = ⊤ // mkEnum t (enum t)
-- 2⟦ PLUS2 T₁ T₂ ⟧   = plus2 2⟦ T₁ ⟧ 2⟦ T₂ ⟧
-- 2⟦ TIMES2 T₁ T₂ ⟧  = times2 2⟦ T₁ ⟧ 2⟦ T₂ ⟧ 

\end{code}

\item Note that 2D types are closed under sums and products but
  \emph{not} under ``division.'' In other words, we cannot form types
  $\fract{(\fract{\tau_1}{\tau_2})}{(\fract{\tau_3}{\tau_4})}$. This is
  why we call our types 2D as we are restricted to two levels.

\item The values of type $\fract{\tau_1}{\tau_2}$ will be denoted
$\fv{v}{\G}$ where $v : \tau_1$ is in white and $\G$ in grey is
essentially the cyclic group $\Z_n$ of order $n=|\tau_2|$. More
precisely, we will think of $\G$ as a particular enumeration of the
elements of $\tau_2$ in some canonical order allowing us to cycle
through the elements.

\item \textbf{Note:} Since we are dealing with finite groups, there
  must exist a bijection $f$ from the carrier of $\G$ to $\{ 1, \ldots
  |\G| \}$, we can define our cycle function:
  \[
    \mathit{cycle}(g) = f^{ -1} ((f(g) + 1) \mod | \G |)
  \]
  And for any group $\G$ and set $S$ we always have the action for all
  $g ∈ \G $, $g(s) = s$ which will give us an action groupoid with
  cardinality $|S|/|\G|$. So actually we can just pick any group with
  the correct order

\item \textbf{Question:} Ok so a value of type $\tau_1/\tau_2$ can be
$\fv{v}{\G}$ for any $v : \tau_1$ and any $\G$ of order
$|\tau_2|$. Wikipedia explains that the number of groups of a given
order is quite a complicated issue and gives the following number of
groups of orders 1 to 30: 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 5, 1, 2, 1,
14, 1, 5, 1, 5, 2, 2, 1, 15, 2, 2, 5, 4, 1, 4. The fact that the
number of groups is difficult to calculate is one thing: the other is
that we need to be able to write down the values of a given type, so
we would need to generate the groups of each order. Moreover it seems
that we have to pick one canonical group as \emph{the} relevant group
of a given order when we create a value of a fractional type using
$\eta$.

\item \textbf{Note:} The types $\fract{\zt}{\tau}$ (including
$\fract{\zt}{\zt}$) are all empty

\item Each type $\fract{\ot}{\tau}$ has one value
$\fv{()}{\G_\tau}$. This group allows us to cycle through the elements
of $\tau$.

\item \textbf{Note:} If the group happens to be isomorphic to $\Z_1$
it has no effect and we recover the plain types from before; the types
$\fract{\tau}{\ot}$ are essentially identical to $\tau$

\item \textbf{Note:} According to our convention, the type
$\fract{\ot}{\zt}$ would have one value $\fv{()}{\G_\zt}$ where
$\G_\zt$ is isomorphic to $\Z_0$; the latter is, by convention, the
infinite cyclic group $\Z$. There is probably no harm in this.

\item The semantic justification for using division is the cardinality
of $\fract{\tau_1}{\tau_2}$ is $|\tau_1|/|\tau_2|$. The reason is that if the
elements of $\tau_1$ are $\{v_1,\ldots,v_{|\tau_1|}\}$, the elements
of $\fract{\tau_1}{\tau_2}$ are $\{ \fv{v_1}{\G_{\tau_2}}, \ldots,
\fv{v_{|\tau_1|}}{\G_{\tau_2}} \}$. This type isomorphic to
$\bigoplus_{|\tau_1|} \fract{\ot}{\tau_2}$

\item We can combine types using $\oplus$ and $\otimes$ in ways that
satisfy the familiar algebraic identities for the rational numbers

\end{itemize}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{2D Pointed Types}
 
\begin{itemize}

\item We now introduce the idea of a \emph{pointed type}
$\pt{\tau}{v}$ which is a non-empty type $\tau$ with one value $v :
\tau$ in focus

\item A pointed type $\pt{\tau}{v}$ can be used anywhere $\tau$ can be
used but we must keep track of what happens to $v$; a transformation
$\tau \rightarrow \tau'$ when acting on the pointed type
$\pt{\tau}{v}$ will map $v$ to some element $v' : \tau'$ and we must
keep track of that in the type.

\item Semantically when we have a type $\fract{1}{\pt{\tau}{v}}$, we have the
group $\G_\tau$ which cycles through the elements of $\tau$ with one
particular value $v$ in focus. We will denote this as $\G_\tau^v$

\item So far we have allowed division by zero. There are general
approaches to dealing with his: the exception monad, meadow axioms
instead of field axioms, or pointed types. The latter seems to lead to
a good operational semantics.

\item Pointed groupoids:

\begin{code}
-- open import Relation.Binary.Core using (Transitive; _⇒_)

-- record Enum• : Set where
--   constructor mkEnum•
--   field
--     t : U•
--     elems : Vec ⟦ carrier t ⟧ ∣ carrier t ∣ 

-- _Enum•×_ : Enum• → Enum• → Enum•
-- (mkEnum• •[ t₁ , p₁ ] elems₁) Enum•× (mkEnum• •[ t₂ , p₂ ] elems₂) =
--   mkEnum•
--     •[ TIMES t₁ t₂ , (p₁ , p₂) ] 
--     (elems₁ enum× elems₂)

-- -- need a proof that every v ∈ ⟦ t ⟧ is in enum t and the index of the position

-- index : {t : U} → (v : ⟦ t ⟧) → Fin ∣ t ∣
-- index = {!!} 

-- record CyclicGroup : Set₁ where
--   constructor cyclic
--   field
--     Carrier : Set
--     ε : Carrier
--     order : ℕ
--     generator : Carrier
--     _∙_ : Carrier → Carrier → Carrier

-- _+₃_ : Fin 3 → Fin 3 → Fin 3
-- zero +₃ y = y
-- suc x +₃ zero = inject+ 1 x
-- suc zero +₃ suc zero = suc (suc zero)
-- suc (suc x) +₃ suc zero = inject+ 2 x
-- suc x +₃ suc (suc zero) = inject+ 1 x
-- suc x +₃ suc (suc (suc ()))

-- ℤ₃ : CyclicGroup
-- ℤ₃ = cyclic (Fin 3) zero 1 zero _+₃_

-- postulate
--   +-comm : (m n : ℕ) → m + n ≡ n + m
--   *-comm : (m n : ℕ) → m * n ≡ n * m

-- associates each value with its index in the canonical enumeration
-- use that to define the cyclic group

-- ind : (t : U) → ⟦ t ⟧ → Fin ∣ t ∣
-- ind ZERO ()
-- ind ONE tt = zero
-- ind (PLUS t₁ t₂) (inj₁ v₁) = inject+ ∣ t₂ ∣ (ind t₁ v₁)
-- ind (PLUS t₁ t₂) (inj₂ v₂) = raise ∣ t₁ ∣ (ind t₂ v₂)
-- ind (TIMES t₁ t₂) (v₁ , v₂) =
--   let d = ind t₁ v₁
--       b = ind t₂ v₂
--       n = ∣ t₁ ∣ 
--       m = ∣ t₂ ∣ 
--   in inject≤
--        (fromℕ (toℕ d * m + toℕ b))
--        (trans≤ (i*n+k≤m*n d b) (refl′ refl))
--   where
--     refl′ : _≡_ ⇒ _≤_
--     refl′ {0} refl = z≤n
--     refl′ {suc m} refl = s≤s (refl′ refl)

--     trans≤ : Transitive _≤_
--     trans≤ z≤n x = z≤n
--     trans≤ (s≤s m≤n) (s≤s n≤o) = s≤s (trans≤ m≤n n≤o)

--     cong+r≤ : ∀ {i j} → i ≤ j → (k : ℕ) → i + k ≤ j + k
--     cong+r≤ {0}     {j}     z≤n       k = n≤m+n j k
--     cong+r≤ {suc i} {0}     ()        k -- absurd
--     cong+r≤ {suc i} {suc j} (s≤s i≤j) k = s≤s (cong+r≤ {i} {j} i≤j k)

--     cong+l≤ : ∀ {i j} → i ≤ j → (k : ℕ) → k + i ≤ k + j
--     cong+l≤ {i} {j} i≤j k =
--       begin (k + i
--                ≡⟨ +-comm k i ⟩ 
--              i + k
--                ≤⟨ cong+r≤ i≤j k ⟩ 
--              j + k
--                ≡⟨ +-comm j k ⟩ 
--              k + j ∎)
--       where open ≤-Reasoning

--     cong*r≤ : ∀ {i j} → i ≤ j → (k : ℕ) → i * k ≤ j * k
--     cong*r≤ {0}     {j}     z≤n       k = z≤n
--     cong*r≤ {suc i} {0}     ()        k -- absurd
--     cong*r≤ {suc i} {suc j} (s≤s i≤j) k = cong+l≤ (cong*r≤ i≤j k) k 

--     sinj≤ : ∀ {i j} → suc i ≤ suc j → i ≤ j
--     sinj≤ {0}     {j}     _        = z≤n
--     sinj≤ {suc i} {0}     (s≤s ()) -- absurd
--     sinj≤ {suc i} {suc j} (s≤s p)  = p

--     i*n+k≤m*n : ∀ {m n} → (i : Fin m) → (k : Fin n) → 
--                 (suc (toℕ i * n + toℕ k) ≤ m * n)
--     i*n+k≤m*n {0} {_} () _
--     i*n+k≤m*n {_} {0} _ ()
--     i*n+k≤m*n {suc m} {suc n} i k = 
--       begin (suc (toℕ i * suc n + toℕ k) 
--             ≡⟨  cong suc (+-comm (toℕ i * suc n) (toℕ k))  ⟩
--             suc (toℕ k + toℕ i * suc n)
--             ≡⟨ refl ⟩
--             suc (toℕ k) + (toℕ i * suc n)
--             ≤⟨ cong+r≤ (bounded k) (toℕ i * suc n) ⟩ 
--             suc n + (toℕ i * suc n)
--             ≤⟨ cong+l≤ (cong*r≤ (sinj≤ (bounded i)) (suc n)) (suc n) ⟩
--             suc n + (m * suc n) 
--             ≡⟨ refl ⟩
--             suc m * suc n ∎)
--       where open ≤-Reasoning

-- suc t1 * t2 = t2 + t1 * t2

-- and then use enum and Fin.Mod; go back to DIV instead of RECIP

-- direct product of groups
-- _G×_ : Group lzero lzero → Group lzero lzero → Group lzero lzero
-- G G× H = record {
--     Carrier = gC × hC
--   ; _≈_ = λ { (g₁ , h₁) (g₂ , h₂) → g₁ g≈ g₂ × h₁ h≈ h₂ }
--   ; _∙_ = λ { (g₁ , h₁) (g₂ , h₂) → (g₁ g∙ g₂ , h₁ h∙ h₂) }
--   ; ε = (gε , hε)
--   ; _⁻¹ = λ { (g , h) → (g g⁻¹ , h h⁻¹) } 
--   ; isGroup = {!!}
--   }
--   where
--     open Group G
--       renaming (Carrier to gC;
--                 _≈_ to _g≈_;
--                 _∙_ to _g∙_;
--                 ε to gε;
--                 _⁻¹ to _g⁻¹; 
--                 isGroup to gisGroup)
--     open Group H
--       renaming (Carrier to hC;
--                 _≈_ to _h≈_;
--                 _∙_ to _h∙_;
--                 ε to hε;
--                 _⁻¹ to _h⁻¹; 
--                 isGroup to hisGroup)

-- 2Group : U• → Group lzero lzero
-- 2Group •[ ZERO , () ]
-- 2Group •[ ONE , tt ] = record {
--     Carrier = ⊤
--   ; _≈_ = {!!} -- _≡_
--   ; _∙_ = λ _ _ → tt
--   ; ε = tt
--   ; _⁻¹ = λ _ → tt
--   ; isGroup = {!!} 
--   }
-- 2Group •[ PLUS t₁ t₂ , inj₁ v₁ ] =
--   let G = 2Group •[ t₁ , v₁ ]
--   in record {
--     Carrier = Group.Carrier G ⊎ ⟦ t₂ ⟧
--   ; _≈_ = {!!}
--   ; _∙_ = {!!}
--   ; ε = {!!}
--   ; _⁻¹ = {!!}
--   ; isGroup = {!!} 
--   }

-- 2Group •[ PLUS t₁ t₂ , inj₂ v₂ ] = 2Group •[ t₂ , v₂ ] -- ...
-- 2Group •[ TIMES t₁ t₂ , (v₁ , v₂) ] = 2Group •[ t₁ , v₁ ] G× 2Group •[ t₂ , v₂ ] 

-- --

-- record ActionGroupoid• : Set₁ where
--   constructor _//•_
--   field
--     S : Set
--     G : Enum•

-- plus2• : ActionGroupoid• → ActionGroupoid• → ActionGroupoid•
-- plus2• (S₁ //• enum₁) (S₂ //• enum₂) = 
--   ((S₁ × ⟦ U•.carrier (Enum•.t enum₂) ⟧) ⊎ (S₂ × ⟦ U•.carrier (Enum•.t enum₁) ⟧)) //•
--   (enum₁ Enum•× enum₂)

-- times2• : ActionGroupoid• → ActionGroupoid• → ActionGroupoid•
-- times2• (S₁ //• enum₁) (S₂ //• enum₂) = 
--   (S₁ × S₂) //• (enum₁ Enum•× enum₂)

-- --

-- data 2D• : Set where
--   DIV•     :  (t₁ : U) → (t₂ : U•) → 2D•
--   PLUS2•   :  2D• → 2D• → 2D•
--   TIMES2•  :  2D• → 2D• → 2D•

-- 2⟦_⟧• : 2D• → ActionGroupoid•
-- 2⟦ DIV• t₁ t₂ ⟧• = ⟦ t₁ ⟧ //• mkEnum• t₂ (enum (carrier t₂))
-- 2⟦ PLUS2• T₁ T₂ ⟧• = plus2• 2⟦ T₁ ⟧• 2⟦ T₂ ⟧•
-- 2⟦ TIMES2• T₁ T₂ ⟧• = times2• 2⟦ T₁ ⟧• 2⟦ T₂ ⟧• 

-- ∣_∣• : 2D• → ℚ
-- ∣ PLUS2• T₁ T₂ ∣• = ∣ T₁ ∣• ℚ+ ∣ T₂ ∣•
-- ∣ TIMES2• T₁ T₂ ∣• = ∣ T₁ ∣• ℚ* ∣ T₂ ∣•
-- ∣ DIV• t₁ •[ t₂ , p₂ ] ∣• = mkRational ∣ t₁ ∣ ∣ t₂ ∣ {pt≠0 •[ t₂ , p₂ ]}
--   where
--     NonZero+ : {m n : ℕ} → NonZero m → NonZero (m + n)
--     NonZero+ {0} {n} m≠0 = ⊥-elim m≠0
--     NonZero+ {suc m} {n} tt = tt  

--     NonZeror+ : {m n : ℕ} → NonZero n → NonZero (m + n)
--     NonZeror+ {m} {0} n≠0 = ⊥-elim n≠0
--     NonZeror+ {0} {suc n} tt = tt
--     NonZeror+ {suc m} {suc n} tt = tt

--     NonZero* : {m n : ℕ} → NonZero m → NonZero n → NonZero (m * n)
--     NonZero* {0} {n} m≠0 n≠0 = ⊥-elim m≠0
--     NonZero* {suc m} {0} m≠0 n≠0 = ⊥-elim n≠0
--     NonZero* {suc m} {suc n} m≠0 n≠0 = tt 

--     pt≠0 : (t : U•) → NonZero ∣ carrier t ∣
--     pt≠0 •[ ZERO , () ] 
--     pt≠0 •[ ONE , p ] = tt
--     pt≠0 •[ PLUS t₁ t₂ , inj₁ x ] with pt≠0 •[ t₁ , x ]
--     ... | t₁≠0 = NonZero+ t₁≠0 
--     pt≠0 •[ PLUS t₁ t₂ , inj₂ y ] with pt≠0 •[ t₂ , y ]
--     ... | t₂≠0 = NonZeror+ {∣ t₁ ∣} t₂≠0 
--     pt≠0 •[ TIMES t₁ t₂ , (x , y) ] with pt≠0 •[ t₁ , x ] | pt≠0 •[ t₂ , y ]
--     ... | t₁≠0 | t₂≠0 = NonZero* t₁≠0 t₂≠0 

\end{code}

\item Examples

\begin{code}
-- Recall pt₁ = •[ PLUS ONE ONE , (inj₁ tt) ]
-- r₁ = show ∣ DIV• (PLUS ONE ONE) pt₁ ∣•             -- "1/1"
-- r₂ = show ∣ DIV• ONE pt₁ ∣•                        -- "1/2"
-- r₃ = show ∣ DIV• (PLUS (PLUS ONE ONE) ONE) pt₁ ∣•  -- "3/2"
\end{code}

\item Semantics: Now we want to relate our definitions to Categories.Groupoid 

\item Then we want to lift combinators to 2D types; check each
combinators is an equivalence of categories; etc.

\end{itemize}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Eta and Epsilon}

\begin{itemize}
\item We can ``create'' and ``cancel'' fractional pointed types using $\eta_{\pt{\tau}{v}}$ and $\epsilon_{\pt{\tau}{v}}$ as follows: 
\[\begin{array}{rcl}
\eta_{\pt{\tau}{v}} &:& \ot \rightarrow \pt{\tau}{v} \otimes 1/\pt{\tau}{v} \\
\eta_{\pt{\tau}{v}}~() &=& (v , \fv{()}{\G^v_{|\tau|}}) \\
\\
\epsilon_{\pt{\tau}{v}} &:& \pt{\tau}{v} \otimes 1/\pt{\tau}{v} \rightarrow \ot \\
\epsilon_{\pt{\tau}{v}}~(v , \fv{()}{\G^v_{|\tau|}}) &=& () 
\end{array}\]
\item Another crucial operation we can do is to use the group to cycle through the values:
\[\begin{array}{rcl}
\cycle &:& \pt{\tau}{v} \otimes 1/\pt{\tau}{v} \rightarrow \pt{\tau}{v'} \otimes 1/\pt{\tau}{v'} \\
\cycle~(v, \fv{()}{\G^v_{|\tau|}}) &=& (v', \fv{()}{\G^{v'}_{|\tau|}})
  \quad \mbox{if~$v'$~is~the~next~value~after~$v$~in~the~cycle~order~of~the~group}
\end{array}\]
\item Let's consider the following algebraic identity and how it would execute in our setting. For $a \neq 0$:
\[\begin{array}{rcl}
a &=& a * 1 \\
&=& a * (1/a * a) \\
&=& (a * 1/a) * a \\
&=& 1 * a \\
&=& a
\end{array}\]
We want to correspond to some transformation $a \rightarrow a$. If $a$ is the empty type, we can't apply this transformation to anything. Otherwise, we start with a value $v : a$, convert it to the pair $(v, ())$, then use $\eta$ to produce $(v , (v' , \fv{()}{\G_a^{v'}}))$ for some value $v' : a$. We know nothing about $v'$; it may be the identical to $v$ or not. Then we reassociate to get $((v , \fv{()}{\G_a^{v'}}), v')$. If $v$ is identical to $v'$ we can use $\epsilon$ to cancel the first pair; if not, we have to re-reassociate, cycle to choose another value and until $v'$ becomes identical to $v$ and then cancel. To summarize:
\[\begin{array}{rcl}
v &\mapsto& (v , ()) \\
&\mapsto& (v , (v' , \fv{()}{\G_a^{v'}})) \\
&\mapsto& ((v , \fv{()}{\G_a^{v'}}), v')  \quad \mbox{stuck~because~} v \neq v' \\
&\mapsto& (v , (v' , \fv{()}{\G_a^{v'}})) \\
&\mapsto& (v , (v , \fv{()}{\G_a^{v}})) \quad \mbox{using~cycle} \\
&\mapsto& ((v , \fv{()}{\G_a^{v}}), v)  \\
&\mapsto& ((), v) \\
&\mapsto& v
\end{array}\]
To make sense of this story, consider that there are two sites; one site has a value $v$ that it wants to communicate to another site. In a conventional situation, the two sites must synchronize but here we have an alternative idea. The second site can speculatively proceed with a guess $v'$ and produce some constraint that can propagate independently that recalls the guess. The second site can in principle proceed further with its guessed value. Meanwhile the constraint reaches the first site and we discover that there is a mismatch. The only
course of action is for the constraint to travel back to the second site, adjust the guess, and continue after the guessed value matches the original value. This idea is reminiscent of our ``reversible concurrency'' paper which discusses much related work. 
\end{itemize}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}

\begin{itemize}

\item An important question arises: what other kinds of finite
  groupoids are out there; this almost calls for a classification of
  finite groupoids which is probably just as bad as classifying finite
  groups. However there are some interesting perspectives from the
  point of complexity theory
  \url{http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.68.7980&rep=rep1&type=pdf}

\end{itemize}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\end{document}

{--
record Typ : Set where
  constructor typ
  field
    carr : U
    len = ∣ carr ∣ 
    auto : Vec (carr ⟷ carr) (ℕsuc len) -- the real magic goes here

    -- normally the stuff below is "global", but here
    -- we attach it to a type.
    id : id⟷ ⇔ (auto !! zero)
    _⊙_ : Fin (ℕsuc len) → Fin (ℕsuc len) → Fin (ℕsuc len)
    coh : ∀ (i j : Fin (ℕsuc len)) → -- note the flip !!!
        ((auto !! i) ◎ (auto !! j) ⇔ (auto !! (j ⊙ i))) 
    -- to get groupoid, we need inverse knowledge, do later
--}

{--
A3 x B5
A0,B0 A0,B1 A0,B2 A0,B3 A0,B4
A1,B0 A1,B1 A0,B2 A1,B3 A1,B4
A2,B0 A2,B1 A0,B2 A2,B3 A2,B4

1,2

1*5 + 2
--}

{--
2Group : U• → Group lzero lzero
2Group •[ t , v₀ ] = record {
    Carrier = ⟦ t ⟧ 
  ; _≈_ = _≡_
  ; _∙_ = λ v₁ v₂ → {!!}
  ; ε = v₀
  ; _⁻¹ = λ v → {!!}
  ; isGroup = {!!} 
  }

2Group : U• → Group lzero lzero
2Group •[ t , v₀ ] = record {
    Carrier = Vec (•[ t , v₀ ] ⟷ •[ t , v₀ ]) ∣ t ∣ 
  ; _≈_ = {!!}
  ; _∙_ = {!!}
  ; ε = {!!}
  ; _⁻¹ = {!!}
  ; isGroup = {!!} 
  }

2Group : U• → Group lzero lzero
2Group •[ t , v₀ ] = record {
    Carrier = ⟦ t ⟧
  ; _≈_ = P._≡_
  ; _∙_ = λ v₁ v₂ → let vs = enum t 
                        i₁ = index v₁
                        i₂ = index v₂
                        i = {!!} -- (toℕ i₁ + toℕ i₂) mod ∣ t ∣ 
                    in lookup i vs
  ; ε = v₀
  ; _⁻¹ = {!!}
  ; isGroup = {!!} 
  }
--}

\begin{code}
{--
2DCat : 2D• → Category lzero lzero lzero
2DCat (DIV• ZERO t) = record {
    Obj  = ⊥
  ; _⇒_  = λ { () () } 
  ; _≡_  = λ { {()} {()} f g }
  ; id   = λ { {()} } 
  ; _∘_  = λ { {()} {()} {()} f g } 
  }
2DCat (DIV• ONE •[ t , p ]) = record {
    Obj  = ⊤
  ; _⇒_  = λ _ _ → ⟦ t ⟧
  ; _≡_  = λ f g → f P.≡ g
  ; id   = p
  ; _∘_  = λ f g → mule (enum t) f g
                   
  }
2DCat (DIV• (PLUS t₁ t₂) t) = {!!}
2DCat (DIV• (TIMES t₁ t₂) t) = {!!}
2DCat (PLUS2• T₁ T₂) = {!!} 
2DCat (TIMES2• T₁ T₂) = {!!} 
--}
\end{code}

\begin{code}

-- The starting point is to treat a permutation as a (singleton) type
-- and show that it corresponds to a groupoid

-- From http://stackoverflow.com/questions/21351906/how-to-define-a-singleton-set
-- and specialized to permutations

-- Perm p is the set that only contains p. 

-- Perm : {τ : U} → (p : τ ⟷ τ) → Set
-- Perm {τ} p = Σ[ p' ∈ (τ ⟷ τ) ] (p' ⇔ p)

-- singleton : {τ : U} → (p : τ ⟷ τ) → Perm p
-- singleton p = (p , id⇔)

-- -- projection

-- fromSingleton : {τ : U} {p : τ ⟷ τ} → Singleton p → (τ ⟷ τ)
-- fromSingleton (p , _) = p

-- starting from v we equate it to every value in its orbit including itself
-- definition below is nonsense

-- _≈_ : {τ : U} {c : τ ⟷ τ} → Rel ⟦ τ ⟧ lzero
-- _≈_ {τ} {c} v₁ v₂ = ap c v₁ P.≡ v₂ ⊎ ap c v₂ P.≡ v₁ 

-- something like

-- data c≈ {τ : U} : (c : τ ⟷ τ) → Rel ⟦ τ ⟧ lzero where
--   step : {v : ⟦ τ ⟧} → (c : τ ⟷ τ) → c≈ c v (ap c v)
--   trans : {v₁ v₂ v₃ : ⟦ τ ⟧} → (c : τ ⟷ τ) → c≈ c v₁ v₂ → c≈ c v₂ v₃ → c≈ c v₁ v₃

-- ≈refl : {τ : U} {v : ⟦ τ ⟧} → (c : τ ⟷ τ) → c≈ c v v
-- ≈refl = {!!} 

-- triv≡ : {τ : U} {c : τ ⟷ τ} {v₁ v₂ : ⟦ τ ⟧} → (f g : c≈ c v₁ v₂) → Set
-- triv≡ _ _ = ⊤

-- triv≡Equiv : {τ : U} {c : τ ⟷ τ} {v₁ v₂ : ⟦ τ ⟧} →
--              IsEquivalence (triv≡ {τ} {c} {v₁} {v₂})
-- triv≡Equiv = record 
--   { refl = tt
--   ; sym = λ _ → tt
--   ; trans = λ _ _ → tt
--   }

-- iterate : {τ : U} {n : ℕ} (p : τ ⟷ τ) (i : Fin n) → (τ ⟷ τ) 
-- iterate p zero = id⟷ 
-- iterate p (suc n) = p ◎ (iterate p n)

-- Iterate : {τ : U} {n : ℕ} (p : τ ⟷ τ) (i : Fin n) → Set
-- Iterate p n = Perm (iterate p n)
  
-- Iterate≡ : {τ : U} → (p : τ ⟷ τ) →
--            (p₁ p₂ : Σ[ n ∈ Fin (suc ∣ τ ∣) ] (Iterate p n)) → Set
-- Iterate≡ p (n₁ , (p₁ , α₁)) (n₂ , (p₂ , α₂)) = (n₁ P.≡ n₂) × (p₁ ⇔ p₂)

-- PtoC : {τ : U} {p : τ ⟷ τ} → Perm p → Category lzero lzero lzero
-- PtoC {τ} (p , α) = record
--   { Obj = ⊤
--   ; _⇒_ = λ _ _ → Σ[ n ∈ Fin (suc ∣ τ ∣) ] (Iterate p n)
--   ; _≡_ = λ p₁ p₂ → Iterate≡ p p₁ p₂ 
--   ; id = (zero , singleton id⟷)
--   ; _∘_ = λ { (m₁ , (p₁ , α₁)) (m₂ , (p₂ , α₂)) → {!!}} 
--   ; assoc = {!!} -- tt
--   ; identityˡ = {!!} -- tt
--   ; identityʳ = {!!} -- tt
--   ; equiv = {!!} -- triv≡Equiv {τ} {p}
--   ; ∘-resp-≡ = {!!} -- λ _ _ → tt
--   }

-- U1toC : U/ 1 → Category lzero lzero lzero
-- U1toC (() ×ⁿ ())
-- U1toC (τ // p) = record
--   { Obj = ⟦ τ ⟧
--   ; _⇒_ = c≈ p 
--   ; _≡_ = triv≡ {τ} {p} 
--   ; id = ≈refl p
--   ; _∘_ = λ y x → trans p x y
--   ; assoc = tt
--   ; identityˡ = tt
--   ; identityʳ = tt
--   ; equiv = triv≡Equiv {τ} {p}
--   ; ∘-resp-≡ = λ _ _ → tt
--   }

-- -- then U/n would have to use some multiplication on groupoids inductively

-- -- toG : (tp : U//) → Groupoid (toC tp)
-- -- toG (τ // p) = record 
-- --   { _⁻¹ = {!!}
-- --   ; iso = record { isoˡ = {!!} ; isoʳ = {!!} } 
-- --   }

-- -- Cardinality

-- ∣_∣/ : {n : ℕ} → (U/ n) → ℚ
-- ∣ ZERO // p ∣/ = + 0 ÷ 1
-- ∣ τ // p ∣/ = {!!}
--   -- for each connected component i, calculate the number of automorphisms ℓᵢ
--   -- return ∑ᵢ 1/ℓᵢ
-- ∣ T₁ ×ⁿ T₂ ∣/ = ∣ T₁ ∣/ ℚ* ∣ T₂ ∣/ 



-- N-dimensional fractional types

-- data U/ : (n : ℕ) → Set where
--   _//_ : {τ₁ τ₂ : U} → (p₁ : τ₁ ⟷ τ₁) → (p₂ : τ₂ ⟷ τ₂)→ U/ 1 -- 1 dimensional
--   _×ⁿ_ : {n : ℕ} → (U/ n) → (U/ n) → (U/ (suc n)) -- n+1 dimensional hypercube

-- ⇑ : U → U/ 1
-- ⇑ τ = τ // id⟷

-- _⊞_ : {n : ℕ} → (U/ n) → (U/ n) → (U/ n)
-- (τ₁ // p₁) ⊞ (τ₂ // p₂) = (PLUS τ₁ τ₂) // (p₁ ⊕ p₂)
-- (τ // p) ⊞ (() ×ⁿ ()) 
-- (() ×ⁿ ()) ⊞ (τ // p) 
-- (T₁ ×ⁿ T₂) ⊞ (T₃ ×ⁿ T₄) = (T₁ ⊞ T₃) ×ⁿ (T₂ ⊞ T₄) 

-- _⊠_ : {m n : ℕ} → (U/ m) → (U/ n) → (U/ (m + n))
-- (τ₁ // p₁) ⊠ (τ₂ // p₂) = (τ₁ // p₁) ×ⁿ (τ₂ // p₂)
-- (τ // p) ⊠ (T₁ ×ⁿ T₂) = ((τ // p) ⊠ T₁) ×ⁿ ((τ // p) ⊠ T₂)
-- (T₁ ×ⁿ T₂) ⊠ T₃ = (T₁ ⊠ T₃) ×ⁿ (T₂ ⊠ T₃)

-- Semantics in Set

-- ⟦_⟧/ : {n : ℕ} → (U/ n) → Set
-- ⟦ τ // p ⟧/ = ⟦ τ ⟧ × Singleton p
-- ⟦ T₁ ×ⁿ T₂ ⟧/ = ⟦ T₁ ⟧/ × ⟦ T₂ ⟧/

-- -- some type examples

-- -- 0-dimensional 

-- BOOL : U
-- BOOL = PLUS ONE ONE

-- THREEL : U
-- THREEL = PLUS BOOL ONE

-- p₁ p₂ p₃ p₄ p₅ p₆ : THREEL ⟷ THREEL
-- p₁ = id⟷ -- (1 2 | 3)
-- p₂ = swap₊ ⊕ id⟷ -- (2 1 | 3)
-- p₃ = assocr₊ ◎ (id⟷ ⊕ swap₊) ◎ assocl₊ -- (1 3 | 2)
-- p₄ = p₂ ◎ p₃ -- (2 3 | 1)
-- p₅ = p₃ ◎ p₂ -- (3 1 | 2)
-- p₆ = p₄ ◎ p₂ -- (3 2 | 1)

-- -- 1-dimensional 

-- T₀ T₁ T₂ T₃ T₄ T₅ T₆ T₇ T₈ T₉ T₁₀ : U/ 1

-- T₀ = ZERO // id⟷
-- T₁ = BOOL // id⟷
-- T₂ = BOOL // swap₊
-- T₃ = THREEL // p₁
-- T₄ = THREEL // p₂
-- T₅ = THREEL // p₃
-- T₆ = THREEL // p₄
-- T₇ = THREEL // p₅
-- T₈ = THREEL // p₆
-- T₉ = (BOOL // swap₊) ⊞ (ONE // id⟷)
-- T₁₀ = (BOOL // swap₊) ⊞ (BOOL // swap₊)

-- -- 2-dimensional 

-- S₁ S₂ : U/ 2

-- S₁ = (BOOL // swap₊) ⊠ (ONE // id⟷)
-- S₂ = (BOOL // swap₊) ⊠ (BOOL // swap₊)

-- -- 3,4,5-dimensional

-- W₁ : U/ 3
-- W₁ = S₁ ⊠ T₁

-- W₂ : U/ 4
-- W₂ = (S₁ ⊠ S₂) ⊞ (W₁ ⊠ T₂)

-- W₃ : U/ 5
-- W₃ = (W₁ ⊠ S₂) ⊞ (T₂ ⊠ W₂)

-- -- examples values

-- x₁ x₂ x₃ : ⟦ T₁ ⟧/
-- x₁ = (inj₁ tt , singleton id⟷)
-- x₂ = (inj₁ tt , (swap₊ ◎ swap₊ , linv◎l))
-- x₃ = (inj₂ tt , singleton id⟷)

-- x₄ x₅ : ⟦ T₂ ⟧/
-- x₄ = (inj₁ tt , singleton swap₊)
-- x₅ = (inj₂ tt , singleton swap₊)

-- x₆ : ⟦ T₉ ⟧/
-- x₆ = (inj₁ (inj₁ tt) , singleton p₂)

-- x₇ : ⟦ S₁ ⟧/
-- x₇ = (inj₁ tt , singleton swap₊) , (tt , singleton id⟷)

-- x₈ : ⟦ S₂ ⟧/
-- x₈ = (inj₁ tt , singleton swap₊) , (inj₂ tt , singleton swap₊)

-- x₉ : ⟦ T₁₀ ⟧/
-- x₉ = (inj₁ (inj₁ tt)  , singleton (swap₊ ⊕ swap₊))

\end{code}

\begin{code}
-- 1-dimensional evaluator; cool how p is maintainted as evaluation progresses

-- eval/1 : {τ₁ τ₂ : U} {p : τ₁ ⟷ τ₁} {q : τ₂ ⟷ τ₂} →
--          (c : τ₁ ⟷ τ₂) → ⟦ τ₁ // p ⟧/ → ⟦ τ₂ // ! c ◎ p ◎ c ⟧/
-- eval/1 c (v , (p' , α)) = (ap c v , (! c ◎ p' ◎ c , id⇔ ⊡ (α ⊡ id⇔)))

-- -- general evaluator subsumes the above
-- -- need n-dimensional combinators

-- data _⟷ⁿ_ : {n : ℕ} → (U/ n) → (U/ n) → Set where
--   base : {τ₁ τ₂ : U} {p : τ₁ ⟷ τ₁} → 
--          (c : τ₁ ⟷ τ₂) → ((τ₁ // p) ⟷ⁿ (τ₂ // (! c ◎ p ◎ c)))
--   hdim : {n : ℕ} {T₁ T₂ T₃ T₄ : U/ n} →
--          (α : T₁ ⟷ⁿ T₃) (β : T₂ ⟷ⁿ T₄) → 
--          (T₁ ×ⁿ T₂) ⟷ⁿ (T₃ ×ⁿ T₄)

-- apⁿ : {n : ℕ} {T₁ T₂ : U/ n} → (cⁿ : T₁ ⟷ⁿ T₂) → ⟦ T₁ ⟧/ → ⟦ T₂ ⟧/
-- apⁿ (base c) (v , (p , α)) = ap c v , (! c ◎ p ◎ c , id⇔ ⊡ (α ⊡ id⇔))
-- apⁿ (hdim cⁿ₁ cⁿ₂) (vⁿ₁ , vⁿ₂) = apⁿ cⁿ₁ vⁿ₁ , apⁿ cⁿ₂ vⁿ₂

\end{code}

This may be helpful \url{http://www.engr.uconn.edu/~vkk06001/report.pdf}

\begin{code}

-- starting from v we equate it to every value in its orbit including itself
-- definition below is nonsense

-- _≈_ : {τ : U} {c : τ ⟷ τ} → Rel ⟦ τ ⟧ lzero
-- _≈_ {τ} {c} v₁ v₂ = ap c v₁ P.≡ v₂ ⊎ ap c v₂ P.≡ v₁ 

-- something like

-- data c≈ {τ : U} : (c : τ ⟷ τ) → Rel ⟦ τ ⟧ lzero where
--   step : {v : ⟦ τ ⟧} → (c : τ ⟷ τ) → c≈ c v (ap c v)
--   trans : {v₁ v₂ v₃ : ⟦ τ ⟧} → (c : τ ⟷ τ) → c≈ c v₁ v₂ → c≈ c v₂ v₃ → c≈ c v₁ v₃

-- ≈refl : {τ : U} {v : ⟦ τ ⟧} → (c : τ ⟷ τ) → c≈ c v v
-- ≈refl = {!!} 

-- triv≡ : {τ : U} {c : τ ⟷ τ} {v₁ v₂ : ⟦ τ ⟧} → (f g : c≈ c v₁ v₂) → Set
-- triv≡ _ _ = ⊤

-- triv≡Equiv : {τ : U} {c : τ ⟷ τ} {v₁ v₂ : ⟦ τ ⟧} →
--              IsEquivalence (triv≡ {τ} {c} {v₁} {v₂})
-- triv≡Equiv = record 
--   { refl = tt
--   ; sym = λ _ → tt
--   ; trans = λ _ _ → tt
--   }

-- U1toC : U/ 1 → Category lzero lzero lzero
-- U1toC (() ×ⁿ ())
-- U1toC (τ // p) = record
--   { Obj = ⟦ τ ⟧
--   ; _⇒_ = c≈ p 
--   ; _≡_ = triv≡ {τ} {p} 
--   ; id = ≈refl p
--   ; _∘_ = λ y x → trans p x y
--   ; assoc = tt
--   ; identityˡ = tt
--   ; identityʳ = tt
--   ; equiv = triv≡Equiv {τ} {p}
--   ; ∘-resp-≡ = λ _ _ → tt
--   }

-- -- then U/n would have to use some multiplication on groupoids inductively

-- -- toG : (tp : U//) → Groupoid (toC tp)
-- -- toG (τ // p) = record 
-- --   { _⁻¹ = {!!}
-- --   ; iso = record { isoˡ = {!!} ; isoʳ = {!!} } 
-- --   }

-- -- Cardinality

-- ∣_∣/ : {n : ℕ} → (U/ n) → ℚ
-- ∣ ZERO // p ∣/ = + 0 ÷ 1
-- ∣ τ // p ∣/ = {!!}
--   -- for each connected component i, calculate the number of automorphisms ℓᵢ
--   -- return ∑ᵢ 1/ℓᵢ
-- ∣ T₁ ×ⁿ T₂ ∣/ = ∣ T₁ ∣/ ℚ* ∣ T₂ ∣/ 


\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Groupoids and Action Groupoids}

In HoTT, types are weak $\infty$-groupoids.

%%%%%
\subsection{Types in HoTT}

Assume we have a collection of points $x_i$ and a collection of
initial edges (paths or identities or equivalences) connecting these
points. As an axiom, we have special paths $\refl~x_i$ between every
point $x_i$ and itself. Using the induction principle for identity
types, we also have the following generated paths:

\begin{itemize}

\item For every path $p : x_i \equiv x_j$, we have an inverse path $!p
: x_j \equiv x_i$

\item For every pair of paths with a common intermediate point, $p :
x_i \equiv x_j$ and $q : x_j \equiv x_k$, we have a composite path $p
\circ q : x_i \equiv x_k$

\end{itemize}

\noindent These generated paths are not all independent; again using
the induction principle for identity types, we can prove for
appropriate starting and ending points:

\begin{itemize}
\item $\gamma_1 : p \circ \refl \equiv p$
\item $\gamma_2 : \refl \circ q \equiv q$
\item $\gamma_3 : ~!p \circ p \equiv \refl$
\item $\gamma_4 : p ~\circ~ !p \equiv \refl$
\item $\gamma_5 : ~! ~(! p) \equiv p$
\item $\gamma_6 : (p \circ q) \circ r \equiv p \circ (q \circ r)$
\item $\gamma_7 : ~! (p \circ q) \equiv ~! q ~\circ~ ! p$
\end{itemize}

At this point, we have generated a structure where the paths $p$, $q$,
$r$, etc. can themselves be viewed as ``points'' with the level-2 paths
$\gamma_i$ connecting them. Using the \refl-postulate and the
induction principle for identity types again, we can repeat the
process above to generate the level-2 paths $!\gamma_i$ and
$\gamma_i \circ \gamma_j$ subject to the conditions
$\gamma_i \circ \refl \equiv \gamma_i$ etc. This gives rise to a
level-3 collection of paths and so on ad infinitum.

Generally speaking, an important endeavor in the HoTT context is to
understand and characterize the structure of this hierarchy of
paths. As a simple example, the type with one point and one
non-trivial path (other than \refl) gives rise to a path structure
that is isomorphic to the natural numbers.

Our paper can be seen as characterizing a special class of types at
levels 0 and 1 of the hierarchy that already offers tantalizing new
insights and benefits to programming practice. In more detail, a
0-groupoid is a set, i.e., a collection of points with only
\refl-paths. A strict 1-groupoid takes us to the next level allowing a
collection of points connected by non-trivial paths. We however
explicitly collapse the higher-level structure by interpreting the
identities $\gamma_1 : p ~\circ~ \refl \equiv p$ as \emph{strict}
equalities. Even with this restriction, arbitrary strict 1-groupoids
are as general as all finite groups which makes them interesting but
difficult to capture structurally and computationally. There are
however some interesting special cases within that form, one of which
we explore in detail in this paper. The special case we study is that
of an \emph{action groupoid} defined and explained in the next
section.

%%%%%
\subsection{Groupoids and Groupoid Cardinality}

\begin{definition}[Groupoid]
There are several possible definitions. For our purposes, we define a
groupoid as a category in which every morphism is an isomorphism.
\end{definition}

We are only going to be interested in \emph{finite}
groupoids. Furthermore, we are going to hardwire that equivalence of
morphisms in that category is trivial.

\medskip

\AgdaHide{
\begin{code}
module X where
  open import Level
  open import Categories.Category 
  import Categories.Morphisms
  open import Relation.Binary
    using (Rel; IsEquivalence; module IsEquivalence; Reflexive; Symmetric; Transitive)
    renaming (_⇒_ to _⊆_)
  open import Function using (flip)
  open import Categories.Support.PropositionalEquality
  open import Categories.Support.Equivalence
  open import Categories.Support.EqReasoning
  open import Data.Product
  open import Categories.Groupoid
  
\end{code}}

\begin{definition}[Groupoid Cardinality]
The cardinality of a groupoid $\mathcal{G}$, written $∥ \mathcal{G} ∥$,
is defined as follows:

\medskip

\begin{code}
  -- ∥_∥ : FiniteGroupoid → ℚ
  -- ∥ G ∥ = {!!} 

  -- To calculate this we would need:
  --  - an enumeration of the distinct component of G
  --  - for each component X, the order of the group Aut(X)
\end{code}

\end{definition}

%%%%%
\subsection{Action Groupoids and their Cardinality}

\begin{definition}[Action Groupoid]
An action groupoid $S \rtimes \G$ is constructed from a set $S$ and a
group $\G$.
\end{definition}

Give lots of examples of action groupoids. Explain cardinality.
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Programming with Action Groupoids}

%%%%%
\subsection{$\Pi$-combinators as Groups}

Every $\Pi$-combinator denotes a permutation on finite sets: we will
use such permutations as a proxy for the group we need to build action
groupoids. Thus, we introduce a new type $\tau ~\rtimes~ p$ where $\tau :
U$ is a $\Pi$-type, i.e., a finite set, and $p : \tau' \leftrightarrow
\tau'$ is some permutation on a possibly distinct type $\tau' : U$. 

We view the type $\tau ~\rtimes~ p$ as follows. The permutation $p$
will be viewed as a one point category whose morphisms are $p^0, p^1,
p^2, \ldots, p^{∣p∣}$ where $∣p∣$ is the order of the permutation. The
resulting group will act trivially (using the identity permutation) on
the points of $\tau$. The result will be a groupoid of cardinality
$∣\tau∣/∣p∣$.

We obviously want to build sums and products of these types. Sums will
have to have a common denominator and products will have to keep the
different permutations and collect them giving rise to a notion of
dimension that is essentially the number of independent permutations
we are keeping in the type.

\begin{code}

-- N-dimensional fractional types

-- Turn a particular permutation into a singleton type

-- Perm : {τ : U} → (p : τ ⟷ τ) → Set
-- Perm {τ} p = Σ[ p' ∈ (τ ⟷ τ) ] (p' ⇔ p)

-- singleton : {τ : U} → (p : τ ⟷ τ) → Perm p
-- singleton p = (p , id⇔)

-- data U/ : (n : ℕ) → Set where
--   ⇑ : U → U/ 0
--   _//_ : {n : ℕ} {τ : U} {p : τ ⟷ τ} → (T : U/ n) → Perm p → U/ n
--   _⋊_ : {n : ℕ} {τ : U} {p : τ ⟷ τ} → (T : U/ n) → Perm p → U/ n 
--   _×ⁿ_ : {n : ℕ} → (U/ n) → (U/ n) → (U/ (suc n)) 

-- _⊞_ : {n : ℕ} → (U/ n) → (U/ n) → (U/ n)
-- (τ₁ ⋊ p) ⊞ T = {!!} 
-- T ⊞ (τ₁ ⋊ p) = {!!} 
-- (τ₁ // (p₁ , α₁)) ⊞ (τ₂ // (p₂ , α₂)) =  {!(τ₁ ⋊ (p₂ , α₂)) ⊞ (τ₂ ⋊ (p₁ , α₁))!}  // (p₁ ⊗ p₂ , resp⊗⇔ α₁ α₂) 
-- (τ // p) ⊞ T = {!!} -- (() ×ⁿ ()) 
-- T ⊞ (τ // p) = {!!} -- (() ×ⁿ ())
-- (T₁ ×ⁿ T₂) ⊞ (T₃ ×ⁿ T₄) = (T₁ ⊞ T₃) ×ⁿ (T₂ ⊞ T₄) 

-- _⊠_ : {m n : ℕ} → (U/ m) → (U/ n) → (U/ (m + n))
-- (τ₁ ⋊ p) ⊠ T = {!!} 
-- T ⊠ (τ₁ ⋊ p) = {!!} 
-- (τ₁ // p₁) ⊠ (τ₂ // p₂) = (τ₁ // p₁) ×ⁿ (τ₂ // p₂)
-- (τ // p) ⊠ (T₁ ×ⁿ T₂) = ((τ // p) ⊠ T₁) ×ⁿ ((τ // p) ⊠ T₂)
-- (T₁ ×ⁿ T₂) ⊠ T₃ = (T₁ ⊠ T₃) ×ⁿ (T₂ ⊠ T₃)

-- Semantics in Set

-- ⟦_⟧/ : {n : ℕ} → (U/ n) → Set
-- ⟦ τ // p ⟧/ = ⟦ τ ⟧ × Singleton p
-- ⟦ T₁ ×ⁿ T₂ ⟧/ = ⟦ T₁ ⟧/ × ⟦ T₂ ⟧/

-- -- some type examples

-- -- 0-dimensional 

-- BOOL : U
-- BOOL = PLUS ONE ONE

-- THREEL : U
-- THREEL = PLUS BOOL ONE

-- p₁ p₂ p₃ p₄ p₅ p₆ : THREEL ⟷ THREEL
-- p₁ = id⟷ -- (1 2 | 3)
-- p₂ = swap₊ ⊕ id⟷ -- (2 1 | 3)
-- p₃ = assocr₊ ◎ (id⟷ ⊕ swap₊) ◎ assocl₊ -- (1 3 | 2)
-- p₄ = p₂ ◎ p₃ -- (2 3 | 1)
-- p₅ = p₃ ◎ p₂ -- (3 1 | 2)
-- p₆ = p₄ ◎ p₂ -- (3 2 | 1)

-- -- 1-dimensional 

-- T₀ T₁ T₂ T₃ T₄ T₅ T₆ T₇ T₈ T₉ T₁₀ : U/ 1

-- T₀ = ZERO // id⟷
-- T₁ = BOOL // id⟷
-- T₂ = BOOL // swap₊
-- T₃ = THREEL // p₁
-- T₄ = THREEL // p₂
-- T₅ = THREEL // p₃
-- T₆ = THREEL // p₄
-- T₇ = THREEL // p₅
-- T₈ = THREEL // p₆
-- T₉ = (BOOL // swap₊) ⊞ (ONE // id⟷)
-- T₁₀ = (BOOL // swap₊) ⊞ (BOOL // swap₊)

-- -- 2-dimensional 

-- S₁ S₂ : U/ 2

-- S₁ = (BOOL // swap₊) ⊠ (ONE // id⟷)
-- S₂ = (BOOL // swap₊) ⊠ (BOOL // swap₊)

-- -- 3,4,5-dimensional

-- W₁ : U/ 3
-- W₁ = S₁ ⊠ T₁

-- W₂ : U/ 4
-- W₂ = (S₁ ⊠ S₂) ⊞ (W₁ ⊠ T₂)

-- W₃ : U/ 5
-- W₃ = (W₁ ⊠ S₂) ⊞ (T₂ ⊠ W₂)

-- -- examples values

-- x₁ x₂ x₃ : ⟦ T₁ ⟧/
-- x₁ = (inj₁ tt , singleton id⟷)
-- x₂ = (inj₁ tt , (swap₊ ◎ swap₊ , linv◎l))
-- x₃ = (inj₂ tt , singleton id⟷)

-- x₄ x₅ : ⟦ T₂ ⟧/
-- x₄ = (inj₁ tt , singleton swap₊)
-- x₅ = (inj₂ tt , singleton swap₊)

-- x₆ : ⟦ T₉ ⟧/
-- x₆ = (inj₁ (inj₁ tt) , singleton p₂)

-- x₇ : ⟦ S₁ ⟧/
-- x₇ = (inj₁ tt , singleton swap₊) , (tt , singleton id⟷)

-- x₈ : ⟦ S₂ ⟧/
-- x₈ = (inj₁ tt , singleton swap₊) , (inj₂ tt , singleton swap₊)

-- x₉ : ⟦ T₁₀ ⟧/
-- x₉ = (inj₁ (inj₁ tt)  , singleton (swap₊ ⊕ swap₊))

\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Operational Semantics}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Groupoid Semantics}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{TODO}

\begin{itemize}
\item equivalence of types
\item groupoid interpretation of types
\item equivalence of types interprets as natural transformations which witness
  equivalence of groupoids
\item operational semantics?
\end{itemize}
