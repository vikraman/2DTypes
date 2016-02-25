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

\renewcommand{\AgdaCodeStyle}{\small}
%% shorten the longarrow
\DeclareUnicodeCharacter{10231}{\ensuremath{\leftrightarrow}}
\DeclareUnicodeCharacter{9678}{$\circledcirc$}
\DeclareUnicodeCharacter{8759}{$::$}

\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module frac where
open import Level renaming (suc to lsuc) 
open import Data.Empty
open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Bool
open import Data.Product hiding (map)
open import Data.Vec
open import Data.Nat hiding (_⊔_)
open import Data.Integer using (+_) 
open import Rational+ renaming (_+_ to _ℚ+_; _*_ to _ℚ*_)
open import Function

infixr 30 _⟷_
infixr 10 _◎_
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

\item A type $\tau$ has $|\tau|$ points:

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
  the axioms of commutative rigs

\item If we have combinators $c_1, c_2 : \tau_1\leftrightarrow\tau_2$,
  we have level-2 combinators $\alpha : c_1 \Leftrightarrow c_2$ which
  are (quite messy) equivalences of isomorphisms, and which happen to
  correspond to the coherence conditions for rig groupoids. So far
  these are not needed for the development that follows.

\end{itemize}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{2D-types: Intuition}

In HoTT, types are weak $\infty$-groupoids. In more detail, assume we
have a collection of points $x_i$ and a collection of initial edges
(paths or identities or equivalences) connecting these points. As an
axiom, we have special paths $\refl~x_i$ between every point $x_i$
and itself. Using the induction principle for identity types, we also
have the following generated paths:

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
$r$, etc. can be viewed as ``points'' with the level-2 paths
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
insights and benefits to programming practice. In more detail,
a 0-groupoid is a set, i.e., a collection of points with only
\refl-paths. A strict 1-groupoid takes us to the next level allowing a
collection of points connected by non-trivial paths. We however
explicitly collapse the higher-level structure by interpreting the
identities $\gamma_1 : p ~\circ~ \refl \equiv p$ as \emph{strict}
equalities. Even with this restriction, arbitrary strict 1-groupoids
are as general as all finite groups which makes them still difficult
to capture structurally and computationally. There are however some
interesting special cases within that form, one of which we explore in
detail in this paper. The special case we study is that of an
\emph{action groupoid} $S \rtimes \G$ where $S$ is a set and $\G$ is a
cyclic group. 

Give lots of examples of action groupoids. Explain cardinality.
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Pointed Types} 
 
\begin{itemize}
\item Our first generalization is to introduce \emph{pointed types}. A
  pointed type $\pt{\tau}{v}$ is a non-empty type $\tau$ along
  with one specific value $v : \tau$ that is considered ``in focus.''
  Examples:

{\footnotesize{
\begin{code}
record U• : Set where
  constructor •[_,_]
  field
    carrier : U
    •    : ⟦ carrier ⟧

pt₁ pt₂ pt₃ : U•
pt₁ = •[ PLUS ONE ONE , (inj₁ tt) ]
pt₂ = •[ PLUS ONE ONE , (inj₂ tt) ]
pt₃ = •[ TIMES ONE ONE , (tt , tt) ]
\end{code}
\smallskip

\AgdaHide{
\begin{code}
open U•
\end{code}
}}}

\item Of course we can never build a pointed type whose carrier is the
  empty type.

\item All the combinators $c : \tau_1\leftrightarrow\tau_2$ can be
  lifted to pointed types. See Fig.~\ref{pointedcomb}.
\end{itemize}

{\footnotesize{
\begin{figure*}[ht]
{\setlength{\mathindent}{0cm}
\begin{multicols}{2}
\begin{code} 
data _⟷_ : U• → U• → Set where
  unite₊ : ∀ {t v} → •[ PLUS ZERO t , inj₂ v ] ⟷ •[ t , v ]
  uniti₊ : ∀ {t v} → •[ t , v ] ⟷ •[ PLUS ZERO t , inj₂ v ]
  swap1₊ : ∀ {t₁ t₂ v₁} → 
    •[ PLUS t₁ t₂ , inj₁ v₁ ] ⟷ •[ PLUS t₂ t₁ , inj₂ v₁ ]
  swap2₊ : ∀ {t₁ t₂ v₂} → 
    •[ PLUS t₁ t₂ , inj₂ v₂ ] ⟷ •[ PLUS t₂ t₁ , inj₁ v₂ ]
  assocl1₊ : ∀ {t₁ t₂ t₃ v₁} → 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] ⟷ 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₁ v₁) ]
  assocl2₊ : ∀ {t₁ t₂ t₃ v₂} → 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] ⟷ 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₂ v₂) ]
  assocl3₊ : ∀ {t₁ t₂ t₃ v₃} → 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ] ⟷ 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₂ v₃ ]
  assocr1₊ : ∀ {t₁ t₂ t₃ v₁} → 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₁ v₁) ] ⟷ 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₁ v₁ ] 
  assocr2₊ : ∀ {t₁ t₂ t₃ v₂} → 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₁ (inj₂ v₂) ] ⟷ 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₁ v₂) ] 
  assocr3₊ : ∀ {t₁ t₂ t₃ v₃} → 
             •[ PLUS (PLUS t₁ t₂) t₃ , inj₂ v₃ ] ⟷ 
             •[ PLUS t₁ (PLUS t₂ t₃) , inj₂ (inj₂ v₃) ]
  unite⋆ : ∀ {t v} → •[ TIMES ONE t , (tt , v) ] ⟷ •[ t , v ]
  uniti⋆ : ∀ {t v} → •[ t , v ] ⟷ •[ TIMES ONE t , (tt , v) ] 
  swap⋆ : ∀ {t₁ t₂ v₁ v₂} → 
    •[ TIMES t₁ t₂ , (v₁ , v₂) ] ⟷
    •[ TIMES t₂ t₁ , (v₂ , v₁) ]
  assocl⋆ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → 
            •[ TIMES t₁ (TIMES t₂ t₃) , (v₁ , (v₂ , v₃)) ] ⟷ 
            •[ TIMES (TIMES t₁ t₂) t₃ , ((v₁ , v₂) , v₃) ]
  assocr⋆ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → 
            •[ TIMES (TIMES t₁ t₂) t₃ , ((v₁ , v₂) , v₃) ] ⟷ 
            •[ TIMES t₁ (TIMES t₂ t₃) , (v₁ , (v₂ , v₃)) ]
  distz : ∀ {t v absurd} → 
    •[ TIMES ZERO t , (absurd , v) ] ⟷ •[ ZERO , absurd ]
  factorz : ∀ {t v absurd} → 
    •[ ZERO , absurd ] ⟷ •[ TIMES ZERO t , (absurd , v) ]
  dist1 : ∀ {t₁ t₂ t₃ v₁ v₃} → 
    •[ TIMES (PLUS t₁ t₂) t₃ , (inj₁ v₁ , v₃) ] ⟷ 
    •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₁ (v₁ , v₃) ]
  dist2 : ∀ {t₁ t₂ t₃ v₂ v₃} → 
    •[ TIMES (PLUS t₁ t₂) t₃ , (inj₂ v₂ , v₃) ] ⟷ 
    •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₂ (v₂ , v₃) ]
  factor1 : ∀ {t₁ t₂ t₃ v₁ v₃} → 
    •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₁ (v₁ , v₃) ] ⟷ 
    •[ TIMES (PLUS t₁ t₂) t₃ , (inj₁ v₁ , v₃) ]
  factor2 : ∀ {t₁ t₂ t₃ v₂ v₃} → 
    •[ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) , inj₂ (v₂ , v₃) ] ⟷ 
    •[ TIMES (PLUS t₁ t₂) t₃ , (inj₂ v₂ , v₃) ]
  id⟷ : ∀ {t v} → •[ t , v ] ⟷ •[ t , v ]
  _◎_ : ∀ {t₁ t₂ t₃ v₁ v₂ v₃} → (•[ t₁ , v₁ ] ⟷ •[ t₂ , v₂ ]) → 
    (•[ t₂ , v₂ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ])
  _⊕1_ : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
    (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
    (•[ PLUS t₁ t₂ , inj₁ v₁ ] ⟷ •[ PLUS t₃ t₄ , inj₁ v₃ ])
  _⊕2_ : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
    (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
    (•[ PLUS t₁ t₂ , inj₂ v₂ ] ⟷ •[ PLUS t₃ t₄ , inj₂ v₄ ])
  _⊗_ : ∀ {t₁ t₂ t₃ t₄ v₁ v₂ v₃ v₄} → 
    (•[ t₁ , v₁ ] ⟷ •[ t₃ , v₃ ]) → (•[ t₂ , v₂ ] ⟷ •[ t₄ , v₄ ]) → 
    (•[ TIMES t₁ t₂ , (v₁ , v₂) ] ⟷ •[ TIMES t₃ t₄ , (v₃ , v₄) ])
\end{code}
\end{multicols}}
\caption{Pointed version of $\Pi$-combinators
\label{pointedcomb}}
\end{figure*}
}}

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
group operation maps each value to the next and the last to the first.

\begin{code}
data 2D : Set where
  DIV     :  (t₁ t₂ : U) → 2D
  PLUS2   :  2D → 2D → 2D
  TIMES2  :  2D → 2D → 2D

enum : (t : U) → Vec ⟦ t ⟧ ∣ t ∣ 
enum ZERO = []
enum ONE = tt ∷ []
enum (PLUS t₁ t₂) = map inj₁ (enum t₁) ++ map inj₂ (enum t₂)
enum (TIMES t₁ t₂) = concat (map (λ v₁ → map (λ v₂ → (v₁ , v₂)) (enum t₂)) (enum t₁)) 

record Enum : Set where
  constructor mkEnum
  field
    t : U
    elems : Vec ⟦ t ⟧ ∣ t ∣ 

record ActionGroupoid : Set₁ where
  constructor _//_
  field
    S : Set
    G : Enum

plus2 : ActionGroupoid → ActionGroupoid → ActionGroupoid
plus2 (S₁ // mkEnum t₁ elems₁) (S₂ // mkEnum t₂ elems₂) =
  ((S₁ × ⟦ t₂ ⟧) ⊎ (S₂ × ⟦ t₁ ⟧)) //
  mkEnum (TIMES t₁ t₂) (concat (map (λ v₁ → map (λ v₂ → (v₁ , v₂)) elems₂) elems₁))

times2 : ActionGroupoid → ActionGroupoid → ActionGroupoid
times2 (S₁ // mkEnum t₁ elems₁) (S₂ // mkEnum t₂ elems₂) =
  (S₁ × S₂) //
  mkEnum (TIMES t₁ t₂) (concat (map (λ v₁ → map (λ v₂ → (v₁ , v₂)) elems₂) elems₁))

2⟦_⟧ : 2D → ActionGroupoid
2⟦ DIV t₁ t₂ ⟧ = ⟦ t₁ ⟧ // mkEnum t₂ (enum t₂)
2⟦ PLUS2 T₁ T₂ ⟧ = plus2 2⟦ T₁ ⟧ 2⟦ T₂ ⟧
2⟦ TIMES2 T₁ T₂ ⟧ = times2 2⟦ T₁ ⟧ 2⟦ T₂ ⟧ 

\end{code}

\item Note that 2D types are closed under sums and products but
  \emph{not} under ``division.'' In other words, we cannot form types
  $\fract{(\fract{\tau_1}{\tau_2})}{(\fract{\tau_3}{\tau_4})}$. This is
  why we call our types 2D as we are restricted to two levels.

\item So far we have allowed division by zero. There are general
approaches to dealing with his: the exception monad, meadow axioms
instead of field axioms, or pointed types. The latter seems to lead to
a good operational semantics.

\item Pointed groupoids:

\begin{code}
data 2D• : Set where
  DIV•     :  (t₁ : U) → (t₂ : U•) → 2D•
  PLUS2•   :  2D• → 2D• → 2D•
  TIMES2•  :  2D• → 2D• → 2D•

record Enum• : Set where
  constructor mkEnum•
  field
    t : U•
    elems : Vec ⟦ carrier t ⟧ ∣ carrier t ∣ -- other than point on focus

record ActionGroupoid• : Set₁ where
  constructor _//•_
  field
    S : Set
    G : Enum•

plus2• : ActionGroupoid• → ActionGroupoid• → ActionGroupoid•
plus2• (S₁ //• mkEnum• •[ t₁ , p₁ ] elems₁) (S₂ //• mkEnum• •[ t₂ , p₂ ] elems₂) =
  ((S₁ × ⟦ t₂ ⟧) ⊎ (S₂ × ⟦ t₁ ⟧)) //•
  mkEnum•
    •[ TIMES t₁ t₂ , (p₁ , p₂) ] 
    (concat (map (λ v₁ → map (λ v₂ → (v₁ , v₂)) elems₂) elems₁))

times2• : ActionGroupoid• → ActionGroupoid• → ActionGroupoid•
times2• (S₁ //• mkEnum• •[ t₁ , p₁ ] elems₁) (S₂ //• mkEnum• •[ t₂ , p₂ ] elems₂) =
  (S₁ × S₂) //•
  mkEnum•
    •[ TIMES t₁ t₂ , (p₁ , p₂) ]
    (concat (map (λ v₁ → map (λ v₂ → (v₁ , v₂)) elems₂) elems₁))

2⟦_⟧• : 2D• → ActionGroupoid•
2⟦ DIV• t₁ t₂ ⟧• = ⟦ t₁ ⟧ //• mkEnum• t₂ (enum (carrier t₂))
2⟦ PLUS2• T₁ T₂ ⟧• = plus2• 2⟦ T₁ ⟧• 2⟦ T₂ ⟧•
2⟦ TIMES2• T₁ T₂ ⟧• = times2• 2⟦ T₁ ⟧• 2⟦ T₂ ⟧• 

pt≠0 : (t : U•) → NonZero ∣ carrier t ∣
pt≠0 •[ ZERO , () ] 
pt≠0 •[ ONE , p ] = tt
pt≠0 •[ PLUS t₁ t₂ , inj₁ x ] with pt≠0 •[ t₁ , x ]
... | t₁≠0 = {!!} 
pt≠0 •[ PLUS t₁ t₂ , inj₂ y ] = {!!}
pt≠0 •[ TIMES t₁ t₂ , p ] = {!!} 

∣_∣• : 2D• → ℚ
∣ DIV• t₁ •[ t₂ , p₂ ] ∣• = mkRational ∣ t₁ ∣ ∣ t₂ ∣ {pt≠0 •[ t₂ , p₂ ]}
∣ PLUS2• T₁ T₂ ∣• = ∣ T₁ ∣• ℚ+ ∣ T₂ ∣•
∣ TIMES2• T₁ T₂ ∣• = ∣ T₁ ∣• ℚ* ∣ T₂ ∣• 
\end{code}

\item Examples

\begin{code}
-- Recall pt₁ = •[ PLUS ONE ONE , (inj₁ tt) ]
-- show ∣ DIV• (PLUS ONE ONE) pt₁ ∣• 
\end{code}

\item The values of type $\fract{\tau_1}{\tau_2}$ will be denoted
$\fv{v}{\G}$ where $v : \tau_1$ is in white and $\G$ in grey is
essentially the cyclic group $\Z_n$ of order $n=|\tau_2|$. More
precisely, we will think of $\G$ as a particular enumeration of the
elements of $\tau_2$ in some canonical order allowing us to cycle
through the elements.

\item \textbf{Note:} Since we are dealing with finite groups, there
  must exist a bijection $f$ from the carrier of $\G$ to $\{ 1, \ldots
  |\G| \}$, we can define our cycle function $cycle(g) =
  f^{-1}((f(g)+1) \% | \G |)$.  And for any group $\G$ and set $S$ we
  always have the action for all $g ∈ \G $, $g(s) = s$ which will give
  us an action groupoid with cardinality $|S|/|\G|$. So actually we
  can just pick any group with the correct order

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
