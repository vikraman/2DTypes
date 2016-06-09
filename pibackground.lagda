%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Background}

The main syntactic vehicle for the technical developments in this paper is a
simple language called $\Pi$ whose only computations are isomorphisms between
finite types~\cite{James:2012:IE:2103656.2103667}. After reviewing the
motivation for this language and its relevance to HoTT, we present its syntax
and semantics.

\begin{figure*}[ht]
\[\begin{array}{cc}
\begin{array}{rrcll}
\unitepl :&  \zt \oplus \tau & \iso & \tau &: \unitipl \\
\unitepr :&  \tau \oplus \zt & \iso & \tau &: \unitipr \\
\swapp :&  \tau_1 \oplus \tau_2 & \iso & \tau_2 \oplus \tau_1 &: \swapp \\
\assoclp :&  \tau_1 \oplus (\tau_2 \oplus \tau_3) & \iso & (\tau_1 \oplus \tau_2) \oplus \tau_3 
  &: \assocrp \\
\\
\unitetl :&  \ot \otimes \tau & \iso & \tau &: \unititl \\
\unitetr :&  \tau \otimes \ot & \iso & \tau &: \unititr \\
\swapt :&  \tau_1 \otimes \tau_2 & \iso & \tau_2 \otimes \tau_1 &: \swapt \\
\assoclt :&  \tau_1 \otimes (\tau_2 \otimes \tau_3) & \iso & (\tau_1 \otimes \tau_2) \otimes \tau_3 
  &: \assocrt \\
\\
\absorbr :&~ \zt \otimes \tau & \iso & \zt &: \factorzl \\
\absorbl :&~ \tau \otimes \zt & \iso & \zt &: \factorzr \\
\dist :&~ (\tau_1 \oplus \tau_2) \otimes \tau_3 & 
  \iso & (\tau_1 \otimes \tau_3) \oplus (\tau_2 \otimes \tau_3)~ &: \factor \\
\distl :&~ \tau_1 \otimes (\tau_2 \oplus \tau_3) & 
  \iso & (\tau_1 \otimes \tau_2) \oplus (\tau_1 \otimes \tau_3)~ &: \factorl 
\end{array}
& 
\begin{minipage}{0.4\textwidth}
\[\begin{array}{c}
\Rule{}
{}
{\jdg{}{}{\idiso : \tau \iso \tau}}
{}
\\
\\
\Rule{}
{\jdg{}{}{c_1 : \tau_1 \iso \tau_2} \quad \vdash c_2 : \tau_2 \iso \tau_3}
{\jdg{}{}{c_1 \odot c_2 : \tau_1 \iso \tau_3}}
{}
\\
\\
\Rule{}
{\jdg{}{}{c_1 : \tau_1 \iso \tau_2} \quad \vdash c_2 : \tau_3 \iso \tau_4}
{\jdg{}{}{c_1 \oplus c_2 : \tau_1 \oplus \tau_3 \iso \tau_2 \oplus \tau_4}}
{}
\\
\\
\Rule{}
{\jdg{}{}{c_1 : \tau_1 \iso \tau_2} \quad \vdash c_2 : \tau_3 \iso \tau_4}
{\jdg{}{}{c_1 \otimes c_2 : \tau_1 \otimes \tau_3 \iso \tau_2 \otimes \tau_4}}
{}
\end{array}\]
\end{minipage}
\end{array}\]
\caption{$\Pi$-combinators~\cite{James:2012:IE:2103656.2103667}
\label{pi-combinators}}
\end{figure*}

\begin{figure*}[ht]
\[\begin{array}{c}
\Rule{}
{c_1 : \tau_1 \iso \tau_2 \quad c_2 : \tau_2 \iso \tau_3 \quad c_3 : \tau_3 \iso \tau_4}
{\jdg{}{}{\assocdl : c_1 \odot (c_2 \odot c_3) \isotwo (c_1 \odot c_2) \odot c_3 : \assocdr}}
{}
\\
\\
\end{array}\]
\caption{$\Pi$-combinators~\cite{James:2012:IE:2103656.2103667}
\label{pi-combinators2}}
\end{figure*}

%%%%%%%%%%%%%%%%%%%%%
\subsection{Reversibility} 

The relevance of reversibility to HoTT is based on the following
analysis. The conventional HoTT approach starts with two, a priori, different
notions: functions and paths, and then postulates an equivalence between a
particular class of functions and paths. As illustrated above, some functions
like \AgdaFunction{not} correspond to paths. Most functions, however, are
evidently unrelated to paths. In particular, any function of type
\AgdaBound{A}~\AgdaSymbol{→}~\AgdaBound{B} that does not have an inverse of
type \AgdaBound{B}~\AgdaSymbol{→}~\AgdaBound{A} cannot have any direct
correspondence to paths as all paths have inverses. An interesting question
then poses itself: since reversible computational models --- in which all
functions have inverses --- are known to be universal computational models,
what would happen if we considered a variant of HoTT based exclusively on
reversible functions?  Presumably in such a variant, all functions --- being
reversible --- would potentially correspond to paths and the distinction
between the two notions would vanish making the univalence postulate
unnecessary. This is the precise technical idea we investigate in detail in
the remainder of the paper.

%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Syntax and Operational Semantics of $\Pi$}
\label{opsempi}

The $\Pi$ family of languages is based on type isomorphisms. In the variant
we consider, the set of types $\tau$ includes the empty type $\zt$, the unit type
$\ot$, and conventional sum and product types. The values classified by these
types are the conventional ones: $\unitv$ of type $\ot$, $\inl{v}$ and $\inr{v}$ for
injections into sum types, and $(v_1,v_2)$ for product types:
\[\begin{array}{lrcl}
(\textit{Types}) & 
  \tau &::=& \zt \alt \ot \alt \tau_1 \oplus \tau_2 \alt \tau_1 \otimes \tau_2 \\
(\textit{L1 Combinator types}) &&& \tau_1 \iso \tau_2 \\
(\textit{L2 Combinator types}) &&& (\tau_1 \iso \tau_2) \isotwo (\tau_1 \iso \tau_2) \\
(\textit{Values}) & 
  v &::=& \unitv \alt \inl{v} \alt \inr{v} \alt (v_1,v_2) \\
(\textit{L1 Combinators}) & 
  c &::=& [\textit{see Fig.~\ref{pi-combinators}}] \\
(\textit{L2 Combinators}) & 
  \alpha &::=& [\textit{see Fig.~\ref{pi-combinators2}}]
\end{array}\]
The interesting syntactic category of $\Pi$ is that of \emph{combinators}
which are witnesses for type isomorphisms $\tau_1 \iso \tau_2$. They consist
of base combinators (on the left side of Fig.~\ref{pi-combinators}) and
compositions (on the right side of the same figure). Each line of the figure
on the left introduces a pair of dual constants\footnote{where $\swapp$ and
$\swapt$ are self-dual.} that witness the type isomorphism in the
middle. This set of isomorphisms is known to be
complete~\cite{Fiore:2004,fiore-remarks} and the language is universal for
hardware combinational
circuits~\cite{James:2012:IE:2103656.2103667}.\footnote{If recursive types
and a trace operator are added, the language becomes Turing
complete~\cite{James:2012:IE:2103656.2103667,rc2011}. We will not be
concerned with this extension in the main body of this paper but it will be
briefly discussed in the conclusion.}

From the perspective of category theory, the language $\Pi$ models what is
called a \emph{symmetric bimonoidal category} or a \emph{commutative rig
category}. These are categories with two binary operations and satisfying the
axioms of a commutative rig (i.e., a commutative ring without negative
elements also known as a commutative semiring) up to coherent
isomorphisms. And indeed the types of the $\Pi$-combinators are precisely the
commutative semiring axioms. A formal way of saying this is that $\Pi$ is the
\emph{categorification}~\cite{math/9802029} of the natural numbers. A simple
(slightly degenerate) example of such categories is the category of finite
sets and permutations in which we interpret every $\Pi$-type as a finite set,
interpret the values as elements in these finite sets, and interpret the
combinators as permutations. 

\begin{figure*}[ht]
\begin{multicols}{2}
\[\begin{array}{r@{\!}lcl}
%% \evalone{\unitepl}{&(\inl{()})} \\
\evalone{\unitepl}{&(\inr{v})} &=& v \\
\evalone{\unitipl}{&v} &=& \inr{v} \\
\evalone{\unitepr}{&(\inl{v})} &=& v \\
%% \evalone{\unitepr}{&(\inr{()})} \\
\evalone{\unitipr}{&v} &=& \inl{v} \\
\evalone{\swapp}{&(\inl{v})} &=& \inr{v} \\
\evalone{\swapp}{&(\inr{v})} &=& \inl{v} \\
\evalone{\assoclp}{&(\inl{v})} &=& \inl{(\inl{v})} \\
\evalone{\assoclp}{&(\inr{(\inl{v})})} &=& \inl{(\inr{v})} \\
\evalone{\assoclp}{&(\inr{(\inr{v})})} &=& \inr{v} \\
\evalone{\assocrp}{&(\inl{(\inl{v})})} &=& \inl{v} \\
\evalone{\assocrp}{&(\inl{(\inr{v})})} &=& \inr{(\inl{v})} \\
\evalone{\assocrp}{&(\inr{v})} &=& \inr{(\inr{v})} \\
\\
\evalone{\unitetl}{&(\unitv,v)} &=& v \\
\evalone{\unititl}{&v} &=& (\unitv,v) \\
\evalone{\unitetr}{&(v,\unitv)} &=& v \\
\evalone{\unititr}{&v} &=& (v,\unitv) \\
\evalone{\swapt}{&(v_1,v_2)} &=& (v_2,v_1) \\
\evalone{\assoclt}{&(v_1,(v_2,v_3))} &=& ((v_1,v_2),v_3) \\
\evalone{\assocrt}{&((v_1,v_2),v_3)} &=& (v_1,(v_2,v_3)) \\
\end{array}\]
\[\begin{array}{r@{\!}lcl}
\evalone{\absorbr}{&(v,\_)} &=& v \\
\evalone{\absorbl}{&(\_,v)} &=& v \\
%% \evalone{\factorzl}{&()} \\
%% \evalone{\factorzr}{&()} \\
\evalone{\dist}{&(\inl{v_1},v_3)} &=& \inl{(v_1,v_3)} \\
\evalone{\dist}{&(\inr{v_2},v_3)} &=& \inr{(v_2,v_3)} \\
\evalone{\factor}{&\inl{(v_1,v_3)}} &=& (\inl{v_1},v_3) \\
\evalone{\factor}{&\inr{(v_2,v_3)}} &=& (\inr{v_2},v_3) \\
\evalone{\distl}{&(v_1,\inl{v_3})} &=& \inl{(v_1,v_3)} \\
\evalone{\distl}{&(v_2,\inr{v_3})} &=& \inr{(v_2,v_3)} \\
\evalone{\factorl}{&\inl{(v_1,v_3)}} &=& (v_1,\inl{v_3}) \\
\evalone{\factorl}{&\inr{(v_2,v_3)}} &=& (v_2,\inr{v_3}) \\
\\
\evalone{\idiso}{&v} &=& v \\
\evalone{(c_1 \odot c_2)}{&v} &=& 
  \evalone{c_2}{(\evalone{c_1}{v})} \\
\evalone{(c_1 \oplus c_2)}{&(\inl{v})} &=& 
  \inl{(\evalone{c_1}{v})} \\
\evalone{(c_1 \oplus c_2)}{&(\inr{v})} &=& 
  \inr{(\evalone{c_2}{v})} \\
\evalone{(c_1 \otimes c_2)}{&(v_1,v_2)} &=& 
  (\evalone{c_1}v_1, \evalone{c_2}v_2) 
\end{array}\]
\end{multicols}
\caption{\label{opsem}Operational Semantics}
\end{figure*}

A couple of examples

In the remainder of this paper, we will be more interested in a model based
on groupoids. But first, we give an operational semantics for $\Pi$.
Operationally, the semantics consists of a pair of mutually recursive
evaluators that take a combinator and a value and propagate the value in the
``forward'' $\triangleright$ direction or in the
``backwards''~$\triangleleft$ direction. We show the complete forward
evaluator in Fig.~\ref{opsem}; the backwards evaluator differs in trivial
ways. 

%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Properties}

Include the definition of $!$

Include the definitions of $<=>$ and $2!$

Also \verb.!!<=>id. and \verb.<=>!.

order

%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Groupoid Model} 

Explain that we only reach a trivial class of groupoids

introduce discreteC and discreteG

Instead of modeling the types of $\Pi$ using sets and the combinators using
permutations we use a semantics that identifies $\Pi$-combinators with
\emph{paths}. More precisely, we model the universe of $\Pi$-types as a space
\AgdaFunction{U} whose points are the individual $\Pi$-types (which are
themselves spaces \AgdaBound{t} containing points). We then postulate that
there is path between the spaces \AgdaBound{t₁} and \AgdaBound{t₂} if there
is a $\Pi$-combinator $c : t_1 \iso t_2$. Our postulate is similar in spirit
to the univalence axiom but, unlike the latter, it has a simple computational
interpretation. A path directly corresponds to a type isomorphism with a
clear operational semantics as presented in the previous section. As we will
explain in more detail below, this approach replaces the datatype
\AgdaSymbol{≡} modeling propositional equality with the datatype
\AgdaSymbol{⟷} modeling type isomorphisms. With this switch, the
$\Pi$-combinators of Fig.~\ref{pi-combinators} become \emph{syntax} for the
paths in the space $U$. Put differently, instead of having exactly one
constructor \AgdaInductiveConstructor{refl} for paths with all other paths
discovered by proofs (see Secs. 2.5--2.12 of the HoTT
book~\citeyearpar{hottbook}) or postulated by the univalence axiom, we have
an \emph{inductive definition} that completely specifies all the paths in the
space $U$.

We begin with the datatype definition of the universe \AgdaFunction{U} of finite
types which are constructed using \AgdaInductiveConstructor{ZERO},
\AgdaInductiveConstructor{ONE}, \AgdaInductiveConstructor{PLUS}, and
\AgdaInductiveConstructor{TIMES}. Each of these finite types will correspond
to a set of points with paths connecting some of the points. The underlying
set of points is computed by \AgdaSymbol{⟦}\_\AgdaSymbol{⟧} as follows:
\AgdaInductiveConstructor{ZERO} maps to the empty set~\AgdaSymbol{⊥},
\AgdaInductiveConstructor{ONE} maps to the singleton set \AgdaSymbol{⊤},
\AgdaInductiveConstructor{PLUS} maps to the disjoint union \AgdaSymbol{⊎},
and \AgdaInductiveConstructor{TIMES} maps to the cartesian product
\AgdaSymbol{×}.

We note that the refinement of the $\Pi$-combinators to combinators on
pointed spaces is given by an inductive family for
\emph{heterogeneous} equality that generalizes the usual inductive
family for propositional equality. Put differently, what used to be
the only constructor for paths \AgdaInductiveConstructor{refl} is now
just one of the many constructors (named
\AgdaInductiveConstructor{id⟷} in the figure). Among the new
constructors we have \AgdaInductiveConstructor{◎} that constructs path
compositions. By construction, every combinator has an inverse
calculated as shown in Fig.~\ref{sym}. These constructions are
sufficient to guarantee that the universe~\AgdaFunction{U} is a
groupoid. Additionally, we have paths that connect values in different
but isomorphic spaces like \ldots

The example \AgdaFunction{notpath} which earlier required the use of the
univalence axiom can now be directly defined using
\AgdaInductiveConstructor{swap1₊} and \AgdaInductiveConstructor{swap2₊}. To
see this, note that \AgdaPrimitiveType{Bool} can be viewed as a shorthand for
\AgdaInductiveConstructor{PLUS} \AgdaInductiveConstructor{ONE}
\AgdaInductiveConstructor{ONE} with \AgdaInductiveConstructor{true} and
\AgdaInductiveConstructor{false} as shorthands for
\AgdaInductiveConstructor{inj₁} \AgdaInductiveConstructor{tt} and
\AgdaInductiveConstructor{inj₂} \AgdaInductiveConstructor{tt}. With this in
mind, the path corresponding to boolean negation consists of two ``fibers'',
one for each boolean value as shown below:

\noindent In other words, a path between spaces is really a collection of
paths connecting the various points. Note however that we never need to
``collect'' these paths using a universal quantification.

Shouldn't we also show that \AgdaPrimitiveType{Bool} contains exactly
$2$ things, and that TRUE and FALSE are ``different''? The other thing
is, whereas not used to be a path between Bool and Bool, we no longer
have that.  Shouldn't we show that, somehow, BOOL and BOOL.F 'union'
BOOL.T are somehow ``equivalent''?  And there there is a coherent
notpath built the same way?  Especially since I am sure it is quite
easy to build incoherent sets of paths!

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module pibackground where

open import Data.Empty using (⊥) 
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true; _∧_; if_then_else_)
open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Data.Nat.LCM using (lcm)
open import Rational+ using (NonZero)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Vec
  using (Vec; []; _∷_; _++_; concat; foldr)
  renaming (map to mapV)

open import Function using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Universe using (Universe)

infix  30 _⟷_
infix  30 _⇔_
infixr 50 _◎_

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\amr{Given that everything is mutually recursive, I suggest this
section to be presented in the mathematical metlanguage, not in
Agda. So let's remove all Agda code and explain the ideas.}

%%%%%
\subsection{$\Pi$ Syntax} 

Types FT, programs $⟷$, and equivalences $⇔$.

\begin{code} 

data FT : Set where
  ZERO   : FT
  ONE    : FT
  PLUS   : FT → FT → FT
  TIMES  : FT → FT → FT

data _⟷_ : FT → FT → Set where
  unite₊l : ∀ {t} → PLUS ZERO t ⟷ t
  uniti₊l : ∀ {t} → t ⟷ PLUS ZERO t
  unite₊r : ∀ {t} → PLUS t ZERO ⟷ t
  uniti₊r : ∀ {t} → t ⟷ PLUS t ZERO
  swap₊   : ∀ {t₁ t₂} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
  assocl₊ : ∀ {t₁ t₂ t₃} →
    PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
  assocr₊ : ∀ {t₁ t₂ t₃} →
    PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
  unite⋆l  : ∀ {t} → TIMES ONE t ⟷ t
  uniti⋆l  : ∀ {t} → t ⟷ TIMES ONE t
  unite⋆r : ∀ {t} → TIMES t ONE ⟷ t
  uniti⋆r : ∀ {t} → t ⟷ TIMES t ONE
  swap⋆   : ∀ {t₁ t₂} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
  assocl⋆ : ∀ {t₁ t₂ t₃} →
    TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
  assocr⋆ : ∀ {t₁ t₂ t₃} →
    TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
  absorbr : ∀ {t} → TIMES ZERO t ⟷ ZERO
  absorbl : ∀ {t} → TIMES t ZERO ⟷ ZERO
  factorzr : ∀ {t} → ZERO ⟷ TIMES t ZERO
  factorzl : ∀ {t} → ZERO ⟷ TIMES ZERO t
  dist    : ∀ {t₁ t₂ t₃} → 
    TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)
  factor  : ∀ {t₁ t₂ t₃} → 
    PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
  distl   : ∀ {t₁ t₂ t₃} →
    TIMES t₁ (PLUS t₂ t₃) ⟷ PLUS (TIMES t₁ t₂) (TIMES t₁ t₃)
  factorl : ∀ {t₁ t₂ t₃} →
    PLUS (TIMES t₁ t₂) (TIMES t₁ t₃) ⟷ TIMES t₁ (PLUS t₂ t₃)
  id⟷    : ∀ {t} → t ⟷ t
  _◎_     : ∀ {t₁ t₂ t₃} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : ∀ {t₁ t₂ t₃ t₄} → 
    (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
  _⊗_     : ∀ {t₁ t₂ t₃ t₄} → 
    (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)

! : {t₁ t₂ : FT} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
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
\end{code}

For $c_1, c_2 : \tau_1\leftrightarrow\tau_2$, we have level-2
combinators $\alpha : c_1 \Leftrightarrow c_2$ which are equivalences
of isomorphisms, and which happen to correspond to the coherence
conditions for rig groupoids. Many of the level 2 combinators not
used. We only present the ones we use in this paper:

\begin{code}
data _⇔_ : {t₁ t₂ : FT} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
  assoc◎l : ∀ {t₁ t₂ t₃ t₄} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} →
    (c₁ ◎ (c₂ ◎ c₃)) ⇔ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r : ∀ {t₁ t₂ t₃ t₄} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} → 
    ((c₁ ◎ c₂) ◎ c₃) ⇔ (c₁ ◎ (c₂ ◎ c₃))
  idl◎l   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    (id⟷ ◎ c) ⇔ c
  idl◎r   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    c ⇔ id⟷ ◎ c
  idr◎l   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    (c ◎ id⟷) ⇔ c
  idr◎r   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    c ⇔ (c ◎ id⟷) 
  id⇔     : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} →
    c ⇔ c
  rinv◎l  : {t₁ t₂ : FT} {c : t₁ ⟷ t₂} → (! c ◎ c) ⇔ id⟷
  rinv◎r  : {t₁ t₂ : FT} {c : t₁ ⟷ t₂} → id⟷ ⇔ (! c ◎ c) 
  linv◎l  : {t₁ t₂ : FT} {c : t₁ ⟷ t₂} → (c ◎ ! c) ⇔ id⟷
  linv◎r  : {t₁ t₂ : FT} {c : t₁ ⟷ t₂} → id⟷ ⇔ (c ◎ ! c) 
  trans⇔  : ∀ {t₁ t₂} {c₁ c₂ c₃ : t₁ ⟷ t₂} → 
    (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  _⊡_  : ∀ {t₁ t₂ t₃} {c₁ c₃ : t₁ ⟷ t₂} {c₂ c₄ : t₂ ⟷ t₃} → 
    (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ◎ c₂) ⇔ (c₃ ◎ c₄)
  resp⊕⇔  : {t₁ t₂ t₃ t₄ : FT} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} → 
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊕ c₂) ⇔ (c₃ ⊕ c₄)
  resp⊗⇔  : {t₁ t₂ t₃ t₄ : FT} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} → 
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊗ c₂) ⇔ (c₃ ⊗ c₄)

2! : {t₁ t₂ : FT} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
2! assoc◎l = assoc◎r
2! assoc◎r = assoc◎l
2! idl◎l = idl◎r
2! idl◎r = idl◎l
2! idr◎l = idr◎r
2! idr◎r = idr◎l
2! rinv◎l = rinv◎r
2! rinv◎r = rinv◎l
2! linv◎l = linv◎r
2! linv◎r = linv◎l
2! id⇔ = id⇔
2! (α ⊡ β) = (2! α) ⊡ (2! β)
2! (trans⇔ α β) = trans⇔ (2! β) (2! α)
2! (resp⊕⇔ α β) = resp⊕⇔ (2! α) (2! β)
2! (resp⊗⇔ α β) = resp⊗⇔ (2! α) (2! β)

\end{code}

%%%%%
\subsection{Semantics}

\begin{code}

-- Denotation as finite sets

UFT : Universe _ _
UFT = record { U = FT; El = ⟦_⟧ }
  where
    ⟦_⟧ : FT → Set
    ⟦ ZERO ⟧         = ⊥ 
    ⟦ ONE ⟧          = ⊤
    ⟦ PLUS t₁ t₂ ⟧   = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
    ⟦ TIMES t₁ t₂ ⟧  = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

open Universe.Universe UFT

-- Operational semantics

postulate
  ap⁻¹ : {t₁ t₂ : FT} → (t₁ ⟷ t₂) → El t₂ → El t₁

ap : {t₁ t₂ : FT} → (t₁ ⟷ t₂) → El t₁ → El t₂
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

\end{code}

%%%%%
\subsection{Properties} 

\begin{code}

postulate 
  ap∼  : {τ : U} {v : El τ} {p₁ p₂ : τ ⟷ τ} →
    (p₁ ⇔ p₂) → ap p₁ v ≡ ap p₂ v
  ap!≡ : {τ : U} {v₁ v₂ : El τ} {p : τ ⟷ τ} →
    (ap p v₁ ≡ v₂) → (ap (! p) v₂ ≡ v₁)
  !!   : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → ! (! c) ≡ c
  ⇔! : {τ₁ τ₂ : U} {p q : τ₁ ⟷ τ₂} → (α : p ⇔ q) → (! p ⇔ ! q)
  !!⇔ : {τ₁ τ₂ : U} {p : τ₁ ⟷ τ₂} → (! (! p) ⇔ p)
\end{code}


%%%%%
\subsection{Order of a Combinator} 

\begin{code}
∣_∣ : U → ℕ
∣ ZERO ∣         = 0
∣ ONE ∣          = 1
∣ PLUS t₁ t₂ ∣   = ∣ t₁ ∣ + ∣ t₂ ∣
∣ TIMES t₁ t₂ ∣  = ∣ t₁ ∣ * ∣ t₂ ∣

elems : (τ : U) → Vec (El τ) ∣ τ ∣ 
elems ZERO = []
elems ONE = tt ∷ []
elems (PLUS τ₁ τ₂) =
  mapV inj₁ (elems τ₁) ++ mapV inj₂ (elems τ₂)
elems (TIMES τ₁ τ₂) =
  concat
    (mapV
      (λ v₁ → mapV (λ v₂ → v₁ , v₂) (elems τ₂))
      (elems τ₁))

lcm' : ℕ → ℕ → ℕ
lcm' i j with lcm i j
... | k , _ = k

_==_ : {τ : U} → El τ → El τ → Bool
_==_ {ZERO} () ()
_==_ {ONE} tt tt = true
_==_ {PLUS τ τ'} (inj₁ x) (inj₁ y) = x == y
_==_ {PLUS τ τ'} (inj₁ x) (inj₂ y) = false
_==_ {PLUS τ τ'} (inj₂ x) (inj₁ y) = false
_==_ {PLUS τ τ'} (inj₂ x) (inj₂ y) = x == y
_==_ {TIMES τ τ'} (x , x') (y , y') = x == y ∧ x' == y'

{-# NON_TERMINATING #-}
order : {τ : U} (p : τ ⟷ τ) → ℕ
order {τ} p = foldr (λ _ → ℕ)
                (λ v o → lcm' o (go τ p v v 1)) 1 (elems τ)
  where go : (τ : U) (p : τ ⟷ τ) → El τ → El τ → ℕ → ℕ
        go τ p v v' n with ap p v'
        ... | v'' = if v == v'' then n else go τ p v v'' (suc n)

postulate
  order-nz : {τ : U} {p : τ ⟷ τ} → NonZero (order p)
  order-!≡ : {τ : U} {p : τ ⟷ τ} →  order p ≡ order (! p)

-- Conjecture:  p ⇔ q   implies  order p = order q
-- Corollary:   p ⇔ !q  implies  order p = order (! q)

-- The opposite is not true.

-- Example
-- p = (1 2 3 4)

-- compose p 0 = compose !p 0 = compose p 4 = compose !p 4
-- 1 -> 1
-- 2 -> 2
-- 3 -> 3
-- 4 -> 4

-- compose p 1  ***     compose !p 1
-- 1 -> 2       ***     1 -> 4
-- 2 -> 3       ***     2 -> 1
-- 3 -> 4       ***     3 -> 2
-- 4 -> 1       ***     4 -> 3

-- compose p 2  ***     compose !p 2
-- 1 -> 3       ***     1 -> 3
-- 2 -> 4       ***     2 -> 4
-- 3 -> 1       ***     3 -> 1
-- 4 -> 2       ***     4 -> 2

-- compose p 3  ***     compose !p 3
-- 1 -> 4       ***     1 -> 2
-- 2 -> 1       ***     2 -> 3
-- 3 -> 2       ***     3 -> 4
-- 4 -> 3       ***     4 -> 1

-- there is a morphism 1 -> 2 using
-- (compose p 1) and (compose !p 3)
-- p¹ is the same as !p³
-- p² is the same as !p²
-- p³ is the same as !p¹

\end{code}

%%%%%
\subsection{Examples}

\begin{code}

BOOL : U
BOOL = PLUS ONE ONE

THREEL : U
THREEL = PLUS BOOL ONE

BOOL² : U
BOOL² = TIMES BOOL BOOL

p₁ p₂ p₃ p₄ p₅ p₆ : THREEL ⟷ THREEL
p₁ = id⟷                                -- (1 2 | 3) has order 1
p₂ = swap₊ ⊕ id⟷                        -- (2 1 | 3) has order 2
p₃ = assocr₊ ◎ (id⟷ ⊕ swap₊) ◎ assocl₊  -- (1 3 | 2) has order 2
p₄ = p₂ ◎ p₃                            -- (2 3 | 1) has order 3
p₅ = p₃ ◎ p₂                            -- (3 1 | 2) has order 3
p₆ = p₄ ◎ p₂                            -- (3 2 | 1) has order 2

NOT : BOOL ⟷ BOOL -- has order 2
NOT = swap₊ 

CNOT : BOOL² ⟷ BOOL² -- has order 2
CNOT = dist ◎ (id⟷ ⊕ (id⟷ ⊗ NOT)) ◎ factor 

TOFFOLI : TIMES BOOL BOOL² ⟷ TIMES BOOL BOOL² -- has order 2
TOFFOLI = dist ◎ (id⟷ ⊕ (id⟷ ⊗ CNOT)) ◎ factor

\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
