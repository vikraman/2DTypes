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
open import Categories.Groupoid.Product using () renaming (Product to GProduct)

-- infix  30 _⇿_

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{$\Pi^/$}

\amr{This now becomes a critical section, where we introduce the
syntax of the language, probably in Agda}

\subsection{Distinguishable Values}

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


