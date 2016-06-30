\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module pifrac where

open import Level renaming (zero to l0)
open import Universe

open import Data.Product hiding (<_,_>)
open import Data.Nat
open import Data.Integer

open import Categories.Category
open import Categories.Groupoid

infix 40 _^_
infix 50 _⊕_
infix 60 _⊗_
infix  30 _⟷_
infix  30 _⇔_
infixr 50 _◎_

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{$\Pi^/$}

We are now ready to turn the semantic treatment of groupoids from the
previous section into an actual programming language. The language
$\Pi^/$ will be an extension of $\Pi$ with new type constructors and
new combinators for creating and manipulating fractional types. Every
computation in $\Pi^/$ will also be information preserving but with
the added expressiveness of being able to create and annihilate
negative information. We use Agda as the appropriate metalanguage in
which to define $\Pi^/$.

%%%%%%%%%%%
\subsection{Types and Combinators}

We begin by defining two mutually recursive syntactic categories
\AgdaRef{U} and \AgdaDatatype{⟷} of types and 1-combinators. The
definitions are identical to the presentation of $\Pi$ in
Sec.~\ref{sec:pi} except for the addition of the type constructors
\AgdaInductiveConstructor{\#} and \AgdaInductiveConstructor{1/\#} that
create order groupoids and inverse order groupoids respectively. We
will introduce additional combinators in proper time. 

{\setlength{\mathindent}{0cm}
\medskip
{\footnotesize{
\begin{code}
mutual
  
  -- Finite types (cf. Sec. 3.1) extended
  -- with #p and 1/#p 

  data U : Set where
    𝟘    : U
    𝟙    : U
    _⊕_  : U → U → U
    _⊗_  : U → U → U
    #    : {τ : U} → (τ ⟷ τ) → U
    1/#  : {τ : U} → (τ ⟷ τ) → U

  -- Combinators (cf. Fig. 2)

  data Prim⟷ : U → U → Set where
    -- additive monoid
    unite₊l :   {t : U} → Prim⟷ (𝟘 ⊕ t) t
    uniti₊l :   {t : U} → Prim⟷ t (𝟘 ⊕ t)
    unite₊r :   {t : U} → Prim⟷ (t ⊕ 𝟘) t
    uniti₊r :   {t : U} → Prim⟷ t (t ⊕ 𝟘)
    swap₊   :   {t₁ t₂ : U} → Prim⟷ (t₁ ⊕ t₂) (t₂ ⊕ t₁)
    assocl₊ :   {t₁ t₂ t₃ : U} →
                Prim⟷ (t₁ ⊕ (t₂ ⊕ t₃))  ((t₁ ⊕ t₂) ⊕ t₃)
    assocr₊ :   {t₁ t₂ t₃ : U} →
                Prim⟷ ((t₁ ⊕ t₂) ⊕ t₃) (t₁ ⊕ (t₂ ⊕ t₃))
    -- multiplicative monoid
    unite⋆l :   {t : U} → Prim⟷ (𝟙 ⊗ t) t
    uniti⋆l :   {t : U} → Prim⟷ t (𝟙 ⊗ t)
    unite⋆r :   {t : U} → Prim⟷ (t ⊗ 𝟙) t
    uniti⋆r :   {t : U} → Prim⟷ t (t ⊗ 𝟙)
    swap⋆   :   {t₁ t₂ : U} → Prim⟷ (t₁ ⊗ t₂) (t₂ ⊗ t₁)
    assocl⋆ :   {t₁ t₂ t₃ : U} →
                Prim⟷ (t₁ ⊗ (t₂ ⊗ t₃)) ((t₁ ⊗ t₂) ⊗ t₃)
    assocr⋆ :   {t₁ t₂ t₃ : U} →
                Prim⟷ ((t₁ ⊗ t₂) ⊗ t₃) (t₁ ⊗ (t₂ ⊗ t₃))
    -- multiplication distributes over addition
    absorbr :   {t : U} → Prim⟷ (𝟘 ⊗ t) 𝟘
    absorbl :   {t : U} → Prim⟷ (t ⊗ 𝟘) 𝟘
    factorzr :  {t : U} → Prim⟷ 𝟘 (t ⊗ 𝟘)
    factorzl :  {t : U} → Prim⟷ 𝟘 (𝟘 ⊗ t)
    dist :      {t₁ t₂ t₃ : U} →
                Prim⟷ ((t₁ ⊕ t₂) ⊗ t₃) ((t₁ ⊗ t₃) ⊕ (t₂ ⊗ t₃))
    factor :    {t₁ t₂ t₃ : U} →
                Prim⟷ ((t₁ ⊗ t₃) ⊕ (t₂ ⊗ t₃)) ((t₁ ⊕ t₂) ⊗ t₃)
    distl :     {t₁ t₂ t₃ : U} →
                Prim⟷ (t₁ ⊗ (t₂ ⊕ t₃)) ((t₁ ⊗ t₂) ⊕ (t₁ ⊗ t₃))
    factorl :   {t₁ t₂ t₃ : U} →
                Prim⟷ ((t₁ ⊗ t₂) ⊕ (t₁ ⊗ t₃)) (t₁ ⊗ (t₂ ⊕ t₃))

  data _⟷_ : U → U → Set where
    Prim :  {t₁ t₂ : U} → (Prim⟷ t₁ t₂) → (t₁ ⟷ t₂)
    id⟷ :   {t : U} → t ⟷ t
    _◎_ :   {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
    _⊕_ :   {t₁ t₂ t₃ t₄ : U} →
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ⊕ t₂ ⟷ t₃ ⊕ t₄)
    _⊗_ :   {t₁ t₂ t₃ t₄ : U} →
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ⊗ t₂ ⟷ t₃ ⊗ t₄)
\end{code}}}}

The complete code also includes definitions for \AgdaFunction{!} which
inverts a 1-combinator, \AgdaDatatype{⇔} which defines equivalences of
1-combinators using 2-combinators, \AgdaFunction{2!} which inverts
2-combinators, and \AgdaFunction{!!⇔id} and \AgdaFunction{⇔!} which
show that 2-combinators commute as expected with inversion of
1-combinators:

{\setlength{\mathindent}{0cm}
\medskip
{\footnotesize{

\begin{code}
! : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
\end{code}
\AgdaHide{
\begin{code}
! (Prim unite₊l)   = Prim uniti₊l
! (Prim uniti₊l)   = Prim unite₊l
! (Prim unite₊r)   = Prim uniti₊r
! (Prim uniti₊r)   = Prim unite₊r
! (Prim swap₊)     = Prim swap₊
! (Prim assocl₊)   = Prim assocr₊
! (Prim assocr₊)   = Prim assocl₊
! (Prim unite⋆l)   = Prim uniti⋆l
! (Prim uniti⋆l)   = Prim unite⋆l
! (Prim unite⋆r)   = Prim uniti⋆r
! (Prim uniti⋆r)   = Prim unite⋆r
! (Prim swap⋆)     = Prim swap⋆
! (Prim assocl⋆)   = Prim assocr⋆
! (Prim assocr⋆)   = Prim assocl⋆
! (Prim absorbl)   = Prim factorzr
! (Prim absorbr)   = Prim factorzl
! (Prim factorzl)  = Prim absorbr
! (Prim factorzr)  = Prim absorbl
! (Prim dist)      = Prim factor
! (Prim factor)    = Prim dist
! (Prim distl)     = Prim factorl
! (Prim factorl)   = Prim distl
! id⟷       = id⟷
! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁
! (c₁ ⊕ c₂) = (! c₁) ⊕ (! c₂)
! (c₁ ⊗ c₂) = (! c₁) ⊗ (! c₂)
\end{code}}

\medskip
\begin{code}
data _⇔_ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set
\end{code}
\AgdaHide{
\begin{code}
  where
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
  rinv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (! c ◎ c) ⇔ id⟷
  rinv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (! c ◎ c)
  linv◎l  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → (c ◎ ! c) ⇔ id⟷
  linv◎r  : {t₁ t₂ : U} {c : t₁ ⟷ t₂} → id⟷ ⇔ (c ◎ ! c)
  trans⇔  : ∀ {t₁ t₂} {c₁ c₂ c₃ : t₁ ⟷ t₂} →
    (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  _⊡_  : ∀ {t₁ t₂ t₃} {c₁ c₃ : t₁ ⟷ t₂} {c₂ c₄ : t₂ ⟷ t₃} →
    (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ◎ c₂) ⇔ (c₃ ◎ c₄)
  resp⊕⇔  : {t₁ t₂ t₃ t₄ : U}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊕ c₂) ⇔ (c₃ ⊕ c₄)
  resp⊗⇔  : {t₁ t₂ t₃ t₄ : U}
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊗ c₂) ⇔ (c₃ ⊗ c₄)
  hom⊕◎⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
        ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⇔ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
  hom◎⊕⇔ : {t₁ t₂ t₃ t₄ t₅ t₆ : U} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
         ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)) ⇔ ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄))
  split⊕-id⟷ : {t₁ t₂ : U} → id⟷ {t₁ ⊕ t₂} ⇔ id⟷ ⊕ id⟷
  id⟷⊕id⟷⇔ : {t₁ t₂ : U} → (id⟷ {t₁} ⊕ id⟷ {t₂}) ⇔ id⟷
\end{code}}

\medskip
\begin{code}
2! : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
\end{code}
\AgdaHide{
\begin{code}
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
2! hom⊕◎⇔ = hom◎⊕⇔
2! hom◎⊕⇔ = hom⊕◎⇔
2! split⊕-id⟷ = id⟷⊕id⟷⇔
2! id⟷⊕id⟷⇔ = split⊕-id⟷ 

!!⇔prim : {t₁ t₂ : U} → (p : Prim⟷ t₁ t₂) → Prim p ⇔ (! (! (Prim p)))
!!⇔prim unite₊l = id⇔
!!⇔prim uniti₊l = id⇔
!!⇔prim unite₊r = id⇔
!!⇔prim uniti₊r = id⇔
!!⇔prim swap₊ = id⇔
!!⇔prim assocl₊ = id⇔
!!⇔prim assocr₊ = id⇔
!!⇔prim unite⋆l = id⇔
!!⇔prim uniti⋆l = id⇔
!!⇔prim unite⋆r = id⇔
!!⇔prim uniti⋆r = id⇔
!!⇔prim swap⋆ = id⇔
!!⇔prim assocl⋆ = id⇔
!!⇔prim assocr⋆ = id⇔
!!⇔prim absorbr = id⇔
!!⇔prim absorbl = id⇔
!!⇔prim factorzr = id⇔
!!⇔prim factorzl = id⇔
!!⇔prim dist = id⇔
!!⇔prim factor = id⇔
!!⇔prim distl = id⇔
!!⇔prim factorl = id⇔
\end{code}}

\medskip
\begin{code}
!!⇔id : {t₁ t₂ : U} → (p : t₁ ⟷ t₂) → p ⇔ ! (! p)
\end{code}
\AgdaHide{
\begin{code}
!!⇔id id⟷ = id⇔
!!⇔id (_⟷_.Prim c) = !!⇔prim c
!!⇔id (p ◎ q) = !!⇔id p ⊡ !!⇔id q
!!⇔id (p _⟷_.⊕ q) = resp⊕⇔ (!!⇔id p) (!!⇔id q)
!!⇔id (p _⟷_.⊗ q) = resp⊗⇔ (!!⇔id p) (!!⇔id q)
\end{code}}

\medskip
\begin{code}
⇔! : {τ₁ τ₂ : U} {p q : τ₁ ⟷ τ₂} → (p ⇔ q) → (! p ⇔ ! q)
\end{code}
\AgdaHide{
\begin{code}
⇔! assoc◎l = assoc◎r
⇔! assoc◎r = assoc◎l
⇔! idl◎l = idr◎l
⇔! idl◎r = idr◎r
⇔! idr◎l = idl◎l
⇔! idr◎r = idl◎r
⇔! id⇔ = id⇔
⇔! rinv◎l = linv◎l
⇔! rinv◎r = linv◎r
⇔! linv◎l = rinv◎l
⇔! linv◎r = rinv◎r
⇔! (trans⇔ q₁ q₂) = trans⇔ (⇔! q₁) (⇔! q₂)
⇔! (q₁ ⊡ q₂) = ⇔! q₂ ⊡ ⇔! q₁
⇔! (resp⊕⇔ q₁ q₂) = resp⊕⇔ (⇔! q₁) (⇔! q₂)
⇔! (resp⊗⇔ q₁ q₂) = resp⊗⇔ (⇔! q₁) (⇔! q₂)
⇔! hom⊕◎⇔ = hom⊕◎⇔
⇔! hom◎⊕⇔ = hom◎⊕⇔
⇔! split⊕-id⟷ = split⊕-id⟷ 
⇔! id⟷⊕id⟷⇔ = id⟷⊕id⟷⇔
\end{code}}}}}

As motivated in the previous section, we will also need to consider
the iterates $p^k$ of combinators $p$ which are $k$-fold compositions
of $p$ and its inverse. These iterates are not independent: there are
only $\ord{p}$ distinct iterates, up to 2-combinator equivalence:

{\setlength{\mathindent}{0cm}
\medskip
{\footnotesize{
\begin{code}
_^_ : {τ : U} → (p : τ ⟷ τ) → (k : ℤ) → (τ ⟷ τ)
p ^ (+ 0)             = id⟷
p ^ (+ (suc k))       = p ◎ (p ^ (+ k))
p ^ -[1+ 0 ]          = ! p
p ^ (-[1+ (suc k) ])  = (! p) ◎ (p ^ -[1+ k ])

record Iter {τ : U} (p : τ ⟷ τ) : Set where
  constructor <_,_,_>
  field
    k : ℤ
    q : τ ⟷ τ
    α : q ⇔ p ^ k
\end{code}}}}  

For our running example using the type $\mathbb{3}$ and the combinator
$a_2$, we can a few iterates of $a_2$ as follows:

{\setlength{\mathindent}{0cm}
\medskip
{\footnotesize{
\begin{code}
𝟛 : U
𝟛 = (𝟙 ⊕ 𝟙) ⊕ 𝟙

a₂ : 𝟛 ⟷ 𝟛
a₂ = Prim swap₊ ⊕ id⟷ 

p^₀ p^₁ p^₂ p^₃ p^₄ p^₅ : Iter a₂
p^₀ = < + 0 , id⟷ , id⇔ > 
p^₁ = < + 0 , id⟷ ◎ id⟷ , idr◎l > 
p^₂ = <  -[1+ 1 ] ,
         id⟷ , 
         trans⇔ split⊕-id⟷
         (trans⇔ (resp⊕⇔ (linv◎r {c = Prim swap₊}) idr◎r)
         (trans⇔ hom⊕◎⇔ id⇔)) >
p^₃ = <  + 2 ,
         id⟷ ,
         trans⇔ split⊕-id⟷
         (trans⇔ (resp⊕⇔ (linv◎r {c = Prim swap₊}) idr◎r)
         (trans⇔ hom⊕◎⇔ (id⇔ ⊡ idr◎r))) >
p^₄ = < -[1+ 0 ] , a₂ , id⇔ > 
p^₅ = < + 1 , a₂ , idr◎r > 
\end{code}}}}  

\noindent Since $a_2$ has order 2, there are only two distinguishable
iterates. The first four iterates are all equivalent to $(a_2)^0$
which is equivalent \AgdaInductiveConstructor{id⟷}. The last two are
both equivalent to $(a_2)^1$ which is equivalent to $a_2$. The
equivalences are explicit in the construction. 

%%%%%%%%%%%
\subsection{Values}

When the types denote sets, it is evident what it means to have a
value of a given type: it is just an element of the set. When types
denote groupoids, it is less clear what it means to have a value,
especially when the total number of values, as reported by the
groupoid cardinality, is a proper fraction. We obviously cannot list
``half a value'' but what we \emph{can} do is to list an integral
number of values and provide an equivalence relation that specifies
which values are distinguishable such that the ultimate counting of
distinguishable values is a fractional amount. The idea is not
uncommon: in the conventional $\lambda$-calculus, we list $\lambda
x.x$ and $\lambda y.y$ as separate values of type $\tau \rightarrow
\tau$ and then provide a separate equivalence relation
($\alpha$-equivalence) to express the fact that these two values are
indistinguishable. The treatment in our setting is similar but richer
as the equivalence relation is not external but is itself part of the
value and the resulting count may be fractional. Formally we define
values as follows:

{\setlength{\mathindent}{0cm}
\medskip
{\footnotesize{
\begin{code}
data Val : (τ : U) → Set where
  ⋆ :       Val 𝟙
  inl :     {τ₁ τ₂ : U} → Val τ₁ → Val (τ₁ ⊕ τ₂)
  inr :     {τ₁ τ₂ : U} → Val τ₂ → Val (τ₁ ⊕ τ₂)
  [_,_] :   {τ₁ τ₂ : U} → Val τ₁ → Val τ₂ → Val (τ₁ ⊗ τ₂)
  comb :    {τ : U} {p : τ ⟷ τ} → (pᵏ : Iter p) →  Val (# p)
  1/comb :  {τ : U} {p : τ ⟷ τ} → (pᵏ : Iter p) → Val (1/# p)
\end{code}}}}

\noindent The first four lines define the conventional values for the
unit, sum, and product types. The last two lines define values of type
$\order{p}$ and $\iorder{p}$ as iterates of $p$. In the case of
$\order{p}$ the iterates are interpreted as ``\emph{programs}'' that
can act on other values and in the case of $\iorder{p}$ the iterates
are interpreted as ``\emph{symmetries}'' that capture similarities in
values. Note that if $p$ has order, say 3, then there are 3 distinct
values of type $\order{p}$ and 3 distinct values of $\iorder{p}$. The
values of type $\order{p}$ apply $p$ for 0, 1, or 2 times to given
value. The values of type $\iorder{p}$ represent the three ``thirds''
of $p$. If the full action of applying $p$ to a value is thought of as
a rotation for example, then applying each third would correspond to
1/3 of a rotation. 

%%%%%%%
\subsection{Additional Combinators}

most combinators do not look at higher components of values:
indistinguishable values are treated the same!

Our aim is to ensure that $G_1$, $G_2$, and $G_3$ are the denotations
of types with $\frac{3}{2}$ values and that the values of these types
are in 1-1 correspondence. 

\begin{definition}[Semantic Values] Given a groupoid $G$, a
  \emph{value} in~$G$ is a pair consisting of an object $v$ and its
  collection $[\alpha_i]_i$ of outgoing morphisms
  $\alpha_i : v \Rightarrow w_i$ for each reachable object $w_i$.
\end{definition}

\noindent The values in each of our three example groupoids in Fig.~\ref{fig:groupoids2} are:
\begin{itemize}
\item Values of $G_1$ are $(a,[\texttt{id}])$ and $(c,[\texttt{id},\swapp])$;
\item Values of $G_2$ are $(a,[\texttt{id},\swapp])$, $(b,[\texttt{id},\swapp])$, and \\
$(c, [\texttt{id}, \swapp])$; 
\item Values of $G_3$ are $(a,[\texttt{id},\swapp])$, $(b,[\texttt{id},\swapp])$, and \\
$(c, [\texttt{id}, \swapp])$.
\end{itemize}

These values can be considered raw values as they are not all
indistinguishable. But we already see that $G_2$ and $G_3$ have the
same raw values and hence can be reasonably considered as
equivalent. To argue that either is also equivalent to $G_1$, we
reason following a monetary analogy: why is a dollar bill (the value
$(a,[\texttt{id}])$ in $G_1$) considered indistinguishable from two
half-dollars (the values $(a,[\texttt{id},\swapp])$ and
$(b,[\texttt{id},\swapp])$ in $G_2$)? Certainly not because we can
find a 1-1 map between one object and two objects but because we have
a process that can transform one collection of values to the other. In
our case, we proceed as follows. Consider the value
$(a,[\texttt{id}])$ in $G_1$; we can add another copy $\texttt{id}$
and refine it to $\swapp\odot\swapp$ to transform the value to
$(a,[\texttt{id},\swapp\odot\swapp])$. We then introduce a new
intermediate object so that the loop $\swapp\odot\swapp])$ from $a$ to
$a$ goes through an intermediate point $b$, i.e., we have a path
$\swapp$ from $a$ to $b$ and a path $\swapp$ from $b$ to $a$. The
result is groupoid $G_2$.

\begin{definition}[Distinguishability] Two \emph{collections of
    values} $\{V_i\}$ and $\{W_j\}$ in $G$ are indistinguishable
  $\{V_i\} \sim \{W_j\}$, if \ldots
  morphisms.
\end{definition}

\amr{formalize the above and then revisit G1, G2, and G3 to formally
  argue that after taking distinguishability into account they all
  have the same distinguishable values and the number of
  distinguishable values is 1.5}

combinators between FT/ types including eta and epsilon

proof that combinators are information preserving

other properties: inverses etc.

Cardinality-preserving combinators: sound, not complete (see
limitations section), consistent.

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

values equivalent tilde tilde

values indistinguishable

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


