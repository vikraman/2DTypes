\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module pifrac where

open import Level
open import Universe

open import Data.Product

open import Categories.Category
open import Categories.Groupoid

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
\end{code}


%%%%%%%%%%%
\subsection{Distinguishable Values}

\begin{code}
! : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
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

data _⇔_ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
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

2! : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
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

-- Properties

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

!!⇔id : {t₁ t₂ : U} → (p : t₁ ⟷ t₂) → p ⇔ ! (! p)
!!⇔id id⟷ = id⇔
!!⇔id (_⟷_.Prim c) = !!⇔prim c
!!⇔id (p ◎ q) = !!⇔id p ⊡ !!⇔id q
!!⇔id (p _⟷_.⊕ q) = resp⊕⇔ (!!⇔id p) (!!⇔id q)
!!⇔id (p _⟷_.⊗ q) = resp⊗⇔ (!!⇔id p) (!!⇔id q)

⇔! : {τ₁ τ₂ : U} {p q : τ₁ ⟷ τ₂} → (p ⇔ q) → (! p ⇔ ! q)
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

--

El : U → Set₁
El t = Σ[ C ∈ Category zero zero zero ] (Groupoid C)

U-univ : Universe _ _
U-univ = record { U = U ; El = El }
\end{code}


Our aim is to ensure that $G_1$, $G_2$, and $G_3$ are the denotations
of types with $\frac{3}{2}$ values and that the values of these types
are in 1-1 correspondence. This raises an immediate puzzling question:
how are we going to express the set of values of these types? We
obviously cannot list ``half a value'' but what we \emph{can} do is to
list an integral number of values and provide an equivalence relation
that specifies which values are distinguishable such that the ultimate
counting of distinguishable values is fractional. The idea is not
uncommon: in the conventional $\lambda$-calculus, we list
$\lambda x.x$ and $\lambda y.y$ as separate values of type
$\tau \rightarrow \tau$ and then provide a separate equivalence
relation ($\alpha$-equivalence) to express the fact that these two
values are indistinguishable. The treatment in our setting is similar
but richer as the equivalence relation is not external but is itself
part of the value and the resulting count may be fractional. Formally
we define values as follows.

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

\medskip

\begin{code}
-- data _⇿_ : FT/ → FT/ → Set where
--   lift : {τ₁ τ₂ : FT} → (p : τ₁ ⟷ τ₂) → (⇑ τ₁ ⇿ ⇑ τ₂)
--   η : {τ : FT} → (p : τ ⟷ τ) → ⇑ ONE ⇿ (# p ⊠ 1/# p)
--   ε : {τ : FT} → (p : τ ⟷ τ) → (# p ⊠ 1/# p) ⇿ ⇑ ONE
--   unite₊l/ : ∀ {T} → (⇑ ZERO ⊞ T) ⇿ T
--   uniti₊l/ : ∀ {T} → T ⇿ (⇑ ZERO ⊞ T) 
--   unite₊r/ : ∀ {T} → (T ⊞ ⇑ ZERO) ⇿ T
--   uniti₊r/ : ∀ {T} → T ⇿ (T ⊞ ⇑ ZERO)
--   swap₊/ : ∀ {T₁ T₂} → (T₁ ⊞ T₂) ⇿ (T₂ ⊞ T₁)
--   assocl₊/ : ∀ {T₁ T₂ T₃} →
--     (T₁ ⊞ (T₂ ⊞ T₃)) ⇿ ((T₁ ⊞ T₂) ⊞ T₃)
--   assocr₊/ : ∀ {T₁ T₂ T₃} →
--     ((T₁ ⊞ T₂) ⊞ T₃) ⇿ (T₁ ⊞ (T₂ ⊞ T₃))
--   unite⋆l/  : ∀ {T} → (⇑ ONE ⊠ T) ⇿ T
--   uniti⋆l/  : ∀ {T} → T ⇿ (⇑ ONE ⊠ T)
--   unite⋆r/ : ∀ {T} → (T ⊠ ⇑ ONE) ⇿ T
--   uniti⋆r/ : ∀ {T} → T ⇿ (T ⊠ ⇑ ONE)
--   swap⋆/   : ∀ {T₁ T₂} → (T₁ ⊠ T₂) ⇿ (T₂ ⊠ T₁)
--   assocl⋆/ : ∀ {T₁ T₂ T₃} →
--     (T₁ ⊠ (T₂ ⊠ T₃)) ⇿ ((T₁ ⊠ T₂) ⊠ T₃)
--   assocr⋆/ : ∀ {T₁ T₂ T₃} →
--     ((T₁ ⊠ T₂) ⊠ T₃) ⇿ (T₁ ⊠ (T₂ ⊠ T₃))
--   absorbr/ : ∀ {T} → (⇑ ZERO ⊠ T) ⇿ ⇑ ZERO
--   absorbl/ : ∀ {T} → (T ⊠ ⇑ ZERO) ⇿ ⇑ ZERO
--   factorzr/ : ∀ {T} → ⇑ ZERO ⇿ (T ⊠ ⇑ ZERO)
--   factorzl/ : ∀ {T} → ⇑ ZERO ⇿ (⇑ ZERO ⊠ T)
--   dist/    : ∀ {T₁ T₂ T₃} → 
--     ((T₁ ⊞ T₂) ⊠ T₃) ⇿ ((T₁ ⊠ T₃) ⊞ (T₂ ⊠ T₃))
--   factor/  : ∀ {T₁ T₂ T₃} → 
--     ((T₁ ⊠ T₃) ⊞ (T₂ ⊠ T₃)) ⇿ ((T₁ ⊞ T₂) ⊠ T₃)
--   distl/   : ∀ {T₁ T₂ T₃} →
--     (T₁ ⊠ (T₂ ⊞ T₃)) ⇿ ((T₁ ⊠ T₂) ⊞ (T₁ ⊠ T₃))
--   factorl/ : ∀ {T₁ T₂ T₃} →
--     ((T₁ ⊠ T₂) ⊞ (T₁ ⊠ T₃)) ⇿ (T₁ ⊠ (T₂ ⊞ T₃))
--   id⇿    : ∀ {T} → T ⇿ T
--   _◎/_     : ∀ {T₁ T₂ T₃} → (T₁ ⇿ T₂) → (T₂ ⇿ T₃) → (T₁ ⇿ T₃)
--   _⊕/_     : ∀ {T₁ T₂ T₃ T₄} → 
--     (T₁ ⇿ T₃) → (T₂ ⇿ T₄) → ((T₁ ⊞ T₂) ⇿ (T₃ ⊞ T₄))
--   _⊗/_     : ∀ {T₁ T₂ T₃ T₄} → 
--     (T₁ ⇿ T₃) → (T₂ ⇿ T₄) → ((T₁ ⊠ T₂) ⇿ (T₃ ⊠ T₄))
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


