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
\section{$\Pi^/$: Types, Values, and Combinators}

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
definition of types is identical to the presentation of $\Pi$ in
Sec.~\ref{sec:pi} except for the addition of the type constructors
\AgdaInductiveConstructor{\#} and \AgdaInductiveConstructor{1/\#} that
create iteration groupoids and inverse order groupoids. The definition of
1-combinators is also identical to the presentation in
Sec.~\ref{sec:pi} except for the addition of
$\AgdaInductiveConstructor{η-}$, $\AgdaInductiveConstructor{η+}$,
$\AgdaInductiveConstructor{ε+}$, and $\AgdaInductiveConstructor{ε-}$.

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
    -- new types
    #    : {τ : U} → (τ ⟷ τ) → U
    1/#  : {τ : U} → (τ ⟷ τ) → U

  -- Combinators (cf. Fig. 2)

  data Prim⟷ : U → U → Set where
    -- additive monoid
    unite₊l :   {τ : U} → Prim⟷ (𝟘 ⊕ τ) τ
    uniti₊l :   {τ : U} → Prim⟷ τ (𝟘 ⊕ τ)
    unite₊r :   {τ : U} → Prim⟷ (τ ⊕ 𝟘) τ
    uniti₊r :   {τ : U} → Prim⟷ τ (τ ⊕ 𝟘)
    swap₊   :   {τ₁ τ₂ : U} → Prim⟷ (τ₁ ⊕ τ₂) (τ₂ ⊕ τ₁)
    assocl₊ :   {τ₁ τ₂ τ₃ : U} →
                Prim⟷ (τ₁ ⊕ (τ₂ ⊕ τ₃))  ((τ₁ ⊕ τ₂) ⊕ τ₃)
    assocr₊ :   {τ₁ τ₂ τ₃ : U} →
                Prim⟷ ((τ₁ ⊕ τ₂) ⊕ τ₃) (τ₁ ⊕ (τ₂ ⊕ τ₃))
    -- multiplicative monoid
    unite⋆l :   {τ : U} → Prim⟷ (𝟙 ⊗ τ) τ
    uniti⋆l :   {τ : U} → Prim⟷ τ (𝟙 ⊗ τ)
    unite⋆r :   {τ : U} → Prim⟷ (τ ⊗ 𝟙) τ
    uniti⋆r :   {τ : U} → Prim⟷ τ (τ ⊗ 𝟙)
    swap⋆   :   {τ₁ τ₂ : U} → Prim⟷ (τ₁ ⊗ τ₂) (τ₂ ⊗ τ₁)
    assocl⋆ :   {τ₁ τ₂ τ₃ : U} →
                Prim⟷ (τ₁ ⊗ (τ₂ ⊗ τ₃)) ((τ₁ ⊗ τ₂) ⊗ τ₃)
    assocr⋆ :   {τ₁ τ₂ τ₃ : U} →
                Prim⟷ ((τ₁ ⊗ τ₂) ⊗ τ₃) (τ₁ ⊗ (τ₂ ⊗ τ₃))
    -- multiplication distributes over addition
    absorbr :   {τ : U} → Prim⟷ (𝟘 ⊗ τ) 𝟘
    absorbl :   {τ : U} → Prim⟷ (τ ⊗ 𝟘) 𝟘
    factorzr :  {τ : U} → Prim⟷ 𝟘 (τ ⊗ 𝟘)
    factorzl :  {τ : U} → Prim⟷ 𝟘 (𝟘 ⊗ τ)
    dist :      {τ₁ τ₂ τ₃ : U} →
                Prim⟷ ((τ₁ ⊕ τ₂) ⊗ τ₃) ((τ₁ ⊗ τ₃) ⊕ (τ₂ ⊗ τ₃))
    factor :    {τ₁ τ₂ τ₃ : U} →
                Prim⟷ ((τ₁ ⊗ τ₃) ⊕ (τ₂ ⊗ τ₃)) ((τ₁ ⊕ τ₂) ⊗ τ₃)
    distl :     {τ₁ τ₂ τ₃ : U} →
                Prim⟷ (τ₁ ⊗ (τ₂ ⊕ τ₃)) ((τ₁ ⊗ τ₂) ⊕ (τ₁ ⊗ τ₃))
    factorl :   {τ₁ τ₂ τ₃ : U} →
                Prim⟷ ((τ₁ ⊗ τ₂) ⊕ (τ₁ ⊗ τ₃)) (τ₁ ⊗ (τ₂ ⊕ τ₃))

  data _⟷_ : U → U → Set where
    Prim :  {τ₁ τ₂ : U} → (Prim⟷ τ₁ τ₂) → (τ₁ ⟷ τ₂)
    id⟷ :   {τ : U} → τ ⟷ τ
    _◎_ :   {τ₁ τ₂ τ₃ : U} → (τ₁ ⟷ τ₂) → (τ₂ ⟷ τ₃) → (τ₁ ⟷ τ₃)
    _⊕_ :   {τ₁ τ₂ τ₃ τ₄ : U} →
            (τ₁ ⟷ τ₃) → (τ₂ ⟷ τ₄) → (τ₁ ⊕ τ₂ ⟷ τ₃ ⊕ τ₄)
    _⊗_ :   {τ₁ τ₂ τ₃ τ₄ : U} →
            (τ₁ ⟷ τ₃) → (τ₂ ⟷ τ₄) → (τ₁ ⊗ τ₂ ⟷ τ₃ ⊗ τ₄)
    -- new combinators
    η- :    {τ : U} → (p : τ ⟷ τ) → 𝟙 ⟷ (1/# p ⊗ # p)
    η+ :    {τ : U} → (p : τ ⟷ τ) → 𝟙 ⟷ (# p ⊗ 1/# p)
    ε+ :    {τ : U} → (p : τ ⟷ τ) → (# p ⊗ 1/# p) ⟷ 𝟙
    ε- :    {τ : U} → (p : τ ⟷ τ) → (1/# p ⊗ # p) ⟷ 𝟙
\end{code}
}}}

The complete code also includes definitions for \AgdaFunction{!} which
inverts a 1-combinator, \AgdaDatatype{⇔} which defines equivalences of
1-combinators using 2-combinators, \AgdaFunction{2!} which inverts
2-combinators, and \AgdaFunction{!!⇔id} and \AgdaFunction{⇔!} which
show that 2-combinators commute as expected with inversion of
1-combinators. The signatures of these additional functions and sets
are given below:

{\setlength{\mathindent}{0cm}
\medskip
{\footnotesize{

\begin{code}
! : {τ₁ τ₂ : U} → (τ₁ ⟷ τ₂) → (τ₂ ⟷ τ₁)
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
! (η- p)    = ε- p
! (η+ p)    = ε+ p
! (ε- p)    = η- p
! (ε+ p)    = η+ p
\end{code}
}

\medskip
\begin{code}
data _⇔_ : {τ₁ τ₂ : U} → (τ₁ ⟷ τ₂) → (τ₁ ⟷ τ₂) → Set
\end{code}
\AgdaHide{
\begin{code}
  where
  assoc◎l : ∀ {τ₁ τ₂ τ₃ τ₄} {c₁ : τ₁ ⟷ τ₂} {c₂ : τ₂ ⟷ τ₃} {c₃ : τ₃ ⟷ τ₄} →
    (c₁ ◎ (c₂ ◎ c₃)) ⇔ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r : ∀ {τ₁ τ₂ τ₃ τ₄} {c₁ : τ₁ ⟷ τ₂} {c₂ : τ₂ ⟷ τ₃} {c₃ : τ₃ ⟷ τ₄} →
    ((c₁ ◎ c₂) ◎ c₃) ⇔ (c₁ ◎ (c₂ ◎ c₃))
  idl◎l   : ∀ {τ₁ τ₂} {c : τ₁ ⟷ τ₂} →
    (id⟷ ◎ c) ⇔ c
  idl◎r   : ∀ {τ₁ τ₂} {c : τ₁ ⟷ τ₂} →
    c ⇔ id⟷ ◎ c
  idr◎l   : ∀ {τ₁ τ₂} {c : τ₁ ⟷ τ₂} →
    (c ◎ id⟷) ⇔ c
  idr◎r   : ∀ {τ₁ τ₂} {c : τ₁ ⟷ τ₂} →
    c ⇔ (c ◎ id⟷)
  id⇔     : ∀ {τ₁ τ₂} {c : τ₁ ⟷ τ₂} →
    c ⇔ c
  rinv◎l  : {τ₁ τ₂ : U} {c : τ₁ ⟷ τ₂} → (! c ◎ c) ⇔ id⟷
  rinv◎r  : {τ₁ τ₂ : U} {c : τ₁ ⟷ τ₂} → id⟷ ⇔ (! c ◎ c)
  linv◎l  : {τ₁ τ₂ : U} {c : τ₁ ⟷ τ₂} → (c ◎ ! c) ⇔ id⟷
  linv◎r  : {τ₁ τ₂ : U} {c : τ₁ ⟷ τ₂} → id⟷ ⇔ (c ◎ ! c)
  _●_  : ∀ {τ₁ τ₂} {c₁ c₂ c₃ : τ₁ ⟷ τ₂} →
    (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  _⊡_  : ∀ {τ₁ τ₂ τ₃} {c₁ c₃ : τ₁ ⟷ τ₂} {c₂ c₄ : τ₂ ⟷ τ₃} →
    (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ◎ c₂) ⇔ (c₃ ◎ c₄)
  resp⊕⇔  : {τ₁ τ₂ τ₃ τ₄ : U}
         {c₁ : τ₁ ⟷ τ₂} {c₂ : τ₃ ⟷ τ₄} {c₃ : τ₁ ⟷ τ₂} {c₄ : τ₃ ⟷ τ₄} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊕ c₂) ⇔ (c₃ ⊕ c₄)
  resp⊗⇔  : {τ₁ τ₂ τ₃ τ₄ : U}
         {c₁ : τ₁ ⟷ τ₂} {c₂ : τ₃ ⟷ τ₄} {c₃ : τ₁ ⟷ τ₂} {c₄ : τ₃ ⟷ τ₄} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊗ c₂) ⇔ (c₃ ⊗ c₄)
  hom⊕◎⇔ : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : U} {c₁ : τ₅ ⟷ τ₁} {c₂ : τ₆ ⟷ τ₂}
        {c₃ : τ₁ ⟷ τ₃} {c₄ : τ₂ ⟷ τ₄} →
        ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⇔ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
  hom◎⊕⇔ : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : U} {c₁ : τ₅ ⟷ τ₁} {c₂ : τ₆ ⟷ τ₂}
        {c₃ : τ₁ ⟷ τ₃} {c₄ : τ₂ ⟷ τ₄} →
         ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)) ⇔ ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄))
  split⊕-id⟷ : {τ₁ τ₂ : U} → id⟷ {τ₁ ⊕ τ₂} ⇔ id⟷ ⊕ id⟷
  id⟷⊕id⟷⇔ : {τ₁ τ₂ : U} → (id⟷ {τ₁} ⊕ id⟷ {τ₂}) ⇔ id⟷
\end{code}
}

\medskip
\begin{code}
2! : {τ₁ τ₂ : U} {c₁ c₂ : τ₁ ⟷ τ₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
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
2! (α ● β) = (2! β) ● (2! α)
2! (resp⊕⇔ α β) = resp⊕⇔ (2! α) (2! β)
2! (resp⊗⇔ α β) = resp⊗⇔ (2! α) (2! β)
2! hom⊕◎⇔ = hom◎⊕⇔
2! hom◎⊕⇔ = hom⊕◎⇔
2! split⊕-id⟷ = id⟷⊕id⟷⇔
2! id⟷⊕id⟷⇔ = split⊕-id⟷ 

!!⇔prim : {τ₁ τ₂ : U} → (p : Prim⟷ τ₁ τ₂) → Prim p ⇔ (! (! (Prim p)))
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
\end{code}
}

\medskip
\begin{code}
!!⇔id : {τ₁ τ₂ : U} → (p : τ₁ ⟷ τ₂) → p ⇔ ! (! p)
\end{code}
\AgdaHide{
\begin{code}
!!⇔id id⟷ = id⇔
!!⇔id (_⟷_.Prim c) = !!⇔prim c
!!⇔id (p ◎ q) = !!⇔id p ⊡ !!⇔id q
!!⇔id (p _⟷_.⊕ q) = resp⊕⇔ (!!⇔id p) (!!⇔id q)
!!⇔id (p _⟷_.⊗ q) = resp⊗⇔ (!!⇔id p) (!!⇔id q)
!!⇔id (η+ p) = id⇔
!!⇔id (η- p) = id⇔
!!⇔id (ε+ p) = id⇔
!!⇔id (ε- p) = id⇔
\end{code}
}

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
⇔! (q₁ ● q₂) = (⇔! q₁) ● (⇔! q₂)
⇔! (q₁ ⊡ q₂) = ⇔! q₂ ⊡ ⇔! q₁
⇔! (resp⊕⇔ q₁ q₂) = resp⊕⇔ (⇔! q₁) (⇔! q₂)
⇔! (resp⊗⇔ q₁ q₂) = resp⊗⇔ (⇔! q₁) (⇔! q₂)
⇔! hom⊕◎⇔ = hom⊕◎⇔
⇔! hom◎⊕⇔ = hom◎⊕⇔
⇔! split⊕-id⟷ = split⊕-id⟷ 
⇔! id⟷⊕id⟷⇔ = id⟷⊕id⟷⇔
\end{code}
}}}}

As motivated in the previous section, we will also need to consider
the singleton type $\sing{p}$ including all combinators equivalent to
$p$ and the type $\iter{p}$ of all the combinators equivalent to
iterates $p^k$:

{\setlength{\mathindent}{0cm}
\medskip
{\footnotesize{
\begin{code}
record Sing {τ : U} (p : τ ⟷ τ) : Set where
  constructor ⟪_,_⟫
  field
    q : τ ⟷ τ
    α : q ⇔ p

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
\end{code}
}}}

For our running example using the type $\mathbb{3}$ and the combinator
$a_2$, we list a few elements of $\sing{a_2}$ and $\iter{a_2}$:

{\setlength{\mathindent}{0cm}
\medskip
{\footnotesize{
\begin{code}
𝟛 : U
𝟛 = (𝟙 ⊕ 𝟙) ⊕ 𝟙

a₂ : 𝟛 ⟷ 𝟛
a₂ = Prim swap₊ ⊕ id⟷ 

id[a₂]² : id⟷ ⇔ a₂ ◎ (a₂ ◎ id⟷)
id[a₂]² =  split⊕-id⟷ ●
           ((resp⊕⇔ (linv◎r {c = Prim swap₊}) idr◎r) ●
           (hom⊕◎⇔ ● (id⇔ ⊡ idr◎r)))

x y z : Sing a₂
x = ⟪ a₂ , id⇔ ⟫
y = ⟪ id⟷ ◎ a₂ , idl◎l ⟫
z = ⟪  a₂ ◎ (Prim assocr₊ ◎ Prim assocl₊) ,
       (id⇔ ⊡ rinv◎l) ● idr◎l ⟫ 

p^₀ p^₁ p^₂ p^₃ p^₄ p^₅ : Iter a₂
p^₀ = < + 0 , id⟷ , id⇔ > 
p^₁ = < + 0 , id⟷ ◎ id⟷ , idr◎l > 
p^₂ = <  -[1+ 1 ] , id⟷ , 
         split⊕-id⟷ ●
         ((resp⊕⇔ (linv◎r {c = Prim swap₊}) idr◎r) ●
         (hom⊕◎⇔ ● id⇔)) >
p^₃ = <  + 2 , id⟷ , id[a₂]² >
p^₄ = < -[1+ 0 ] , a₂ , id⇔ > 
p^₅ = < + 1 , a₂ , idr◎r > 
\end{code}
}}}

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
  comb :    {τ : U} {p : τ ⟷ τ} → Iter p →  Val (# p)
  1/comb :  {τ : U} {p : τ ⟷ τ} → Iter p → Val (1/# p) 
\end{code}
}}}

\noindent The first four lines define the conventional values for the
unit, sum, and product types. The last two lines define values of type
$\order{p}$ and $\iorder{p}$ using the iterates of $p$. In the case of
$\order{p}$, a value $\AgdaInductiveConstructor{comb}(p^k)$ represents
the program $p$ iterated $k$ times. In the case of $\iorder{p}$, a
value $\AgdaInductiveConstructor{1/comb}(p^k)$ represents the
equivalence that $p^k$ can be annihilated to the identity. 

% Formally we declare when two values are indistinguishable using the
% relation below:

% {\setlength{\mathindent}{0cm}
% \medskip
% {\footnotesize{
% \begin{code}
% get-q : {τ : U} {p : τ ⟷ τ} → Val (# p) → τ ⟷ τ
% get-q (comb i) = Iter.q i

% data _≈_ : {τ : U} → Val τ → Val τ → Set where
%   ⋆≈ :     {v w : Val 𝟙} → v ≈ w
%   inj₁≈ :  {τ₁ τ₂ : U} → {v₁ v₂ : Val τ₁} →
%            v₁ ≈ v₂ → inl {τ₁} {τ₂} v₁ ≈ inl v₂
%   inj₂≈ :  {τ₁ τ₂ : U} → {w₁ w₂ : Val τ₂} →
%            w₁ ≈ w₂ → inr {τ₁} {τ₂} w₁ ≈ inr w₂
%   [,]≈ :   {τ₁ τ₂ : U} {v₁ v₂ : Val τ₁} {w₁ w₂ : Val τ₂} →
%            v₁ ≈ v₂ → w₁ ≈ w₂ → [ v₁ , w₁ ] ≈ [ v₂ , w₂ ]
%   #p≈ :    ∀ {τ} {p : τ ⟷ τ} (p^i p^j : Val (# p)) →
%            get-q p^i ◎ ! (get-q p^j) ⇔ id⟷ → p^i ≈ p^j
%   1/#p≈ :  ∀ {τ} {p : τ ⟷ τ} (q : Iter p) → (p₁ p₂ : Sing p) →
%            Sing.q p₁ ◎ ! (Sing.q p₂) ⇔ Iter.q q ◎ ! (Iter.q q) →
%            (1/comb p₁) ≈ (1/comb p₂)
% \end{code}
% }}}
  
% In the case of $\order{p}$ the iterates are
% interpreted as ``\emph{programs}'' that can act on other values and in
% the case of $\iorder{p}$ the iterates are interpreted as
% ``\emph{symmetries}'' that capture similarities of programs. Note that
% if $p$ has order, say 3, then there are 3 distinct values of type
% $\order{p}$ and 3 distinct values of $\iorder{p}$. The values of type
% $\order{p}$ apply $p$ for 0, 1, or 2 times to given value. The values
% of type $\iorder{p}$, say $x$, $y$, and $z$, represent the three
% ``thirds'' of $p$, so that applying $x(y(z(v)))$ has the same effect
% as applying $p(v)$.

% Given the definitions of combinators and values, we can directly
% implement the operational semantics of Fig.~\ref{opsem}. We will
% however present a more involved operational semantics once we
% introduce additional combinators.

% %%%%%%%
% \subsection{Additional Combinators}

% most combinators do not look at higher components of values:
% indistinguishable values are treated the same!

% Our aim is to ensure that $G_1$, $G_2$, and $G_3$ are the denotations
% of types with $\frac{3}{2}$ values and that the values of these types
% are in 1-1 correspondence. 

% \begin{definition}[Semantic Values] Given a groupoid $G$, a
%   \emph{value} in~$G$ is a pair consisting of an object $v$ and its
%   collection $[\alpha_i]_i$ of outgoing morphisms
%   $\alpha_i : v \Rightarrow w_i$ for each reachable object $w_i$.
% \end{definition}

% \noindent The values in each of our three example groupoids in Fig.~\ref{fig:groupoids2} are:
% \begin{itemize}
% \item Values of $G_1$ are $(a,[\texttt{id}])$ and $(c,[\texttt{id},\swapp])$;
% \item Values of $G_2$ are $(a,[\texttt{id},\swapp])$, $(b,[\texttt{id},\swapp])$, and \\
% $(c, [\texttt{id}, \swapp])$; 
% \item Values of $G_3$ are $(a,[\texttt{id},\swapp])$, $(b,[\texttt{id},\swapp])$, and \\
% $(c, [\texttt{id}, \swapp])$.
% \end{itemize}

% These values can be considered raw values as they are not all
% indistinguishable. But we already see that $G_2$ and $G_3$ have the
% same raw values and hence can be reasonably considered as
% equivalent. To argue that either is also equivalent to $G_1$, we
% reason following a monetary analogy: why is a dollar bill (the value
% $(a,[\texttt{id}])$ in $G_1$) considered indistinguishable from two
% half-dollars (the values $(a,[\texttt{id},\swapp])$ and
% $(b,[\texttt{id},\swapp])$ in $G_2$)? Certainly not because we can
% find a 1-1 map between one object and two objects but because we have
% a process that can transform one collection of values to the other. In
% our case, we proceed as follows. Consider the value
% $(a,[\texttt{id}])$ in $G_1$; we can add another copy $\texttt{id}$
% and refine it to $\swapp\odot\swapp$ to transform the value to
% $(a,[\texttt{id},\swapp\odot\swapp])$. We then introduce a new
% intermediate object so that the loop $\swapp\odot\swapp])$ from $a$ to
% $a$ goes through an intermediate point $b$, i.e., we have a path
% $\swapp$ from $a$ to $b$ and a path $\swapp$ from $b$ to $a$. The
% result is groupoid $G_2$.

% \begin{definition}[Distinguishability] Two \emph{collections of
%     values} $\{V_i\}$ and $\{W_j\}$ in $G$ are indistinguishable
%   $\{V_i\} \sim \{W_j\}$, if \ldots
%   morphisms.
% \end{definition}

% \amr{formalize the above and then revisit G1, G2, and G3 to formally
%   argue that after taking distinguishability into account they all
%   have the same distinguishable values and the number of
%   distinguishable values is 1.5}

% combinators between FT/ types including eta and epsilon

% proof that combinators are information preserving

% other properties: inverses etc.

% Cardinality-preserving combinators: sound, not complete (see
% limitations section), consistent.

% \paragraph*{Intermezzo.} The combinators 

% Consistency is defined in the following
% sense: If we allow arbitrary functions then bad things happen as we
% can throw away the negative information for example. In our reversible
% information-preserving framework, the theory is consistent in the
% sense that not all types are identified. This is easy to see as we
% only identify types that have the same cardinality. This is evident
% for all the combinators except for the new ones. For those new ones
% the only subtle situation is with the empty type. Note however that
% there is no way to define 1/0 and no permutation has order 0. For 0 we
% have one permutation id which has order 1. So if we try to use it, we
% will map 1 to 1 times 1/id which is fine. So if we always preserve
% types and trivially 1 and 0 have different cardinalities so there is
% no way to identify them and we are consistent.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


