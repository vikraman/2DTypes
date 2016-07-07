\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module opsem where

open import Level using () renaming (zero to l0; suc to lsuc)
open import Universe using (Universe)
open import Data.Bool
open import Data.Sum hiding ([_,_])
open import Data.Product hiding (<_,_>)
open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; suc)
open import Data.Integer
  using (ℤ; +_; -[1+_])
  renaming (-_ to ℤ-; suc to ℤsuc; _+_ to _ℤ+_)
-- open import Rational+ renaming (_+_ to _ℚ+_; _*_ to _ℚ*_)
--  hiding (_≤_; _≤?_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; subst)
open import Categories.Groupoid.Sum using () renaming (Sum to GSum)
open import Categories.Groupoid.Product using () renaming (Product to GProduct)
open import Function using (case_of_)

open import pifrac

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{$\Pi^/$: Operational Semantics} 

The operational semantics for all the primitive combinators is a
simple transliteration of Fig.~\ref{opsem}. We omit the
straightforward implementation of \AgdaFunction{prim} below:

{\setlength{\mathindent}{0cm}
\medskip
{\footnotesize{
\begin{code}
prim : {τ₁ τ₂ : U} → (Prim⟷ τ₁ τ₂) → Val τ₁ → Val τ₂
\end{code}}}}
\AgdaHide{
\begin{code}
prim = {!!} 
\end{code}
}

The interesting combinators operationally are
$\AgdaInductiveConstructor{η-}$, $\AgdaInductiveConstructor{η+}$,
$\AgdaInductiveConstructor{ε+}$, and
$\AgdaInductiveConstructor{ε-}$. As suggested from the example in
Sec.~2, their implementation requires some kind of synchronization. It
is possible to implement this
operational semantics using more general computational effects such as
reference cells or backtracking. In this section, we instead present a
semantics in which the dependencies are directly expressed as dataflow
constraints using dependent types. The key abstraction is that of a
\emph{tangled product} described below.

%%%%%%%%%
\subsection{Tangled Products}

(these were explained in section 5 ?)

%%%%%%%
\subsection{Interpreter}

\AgdaHide{
\begin{code}
postulate 
  𝓐𝓹⁻¹ : {T₁ T₂ : U} → (T₁ ⟷ T₂) → Val T₂ → Val T₁
\end{code}
}
Before we can define the full interpreter, we first need to define a particular
tangled product (which will be needed by $\AgdaInductiveConstructor{η-}$).
The identity tangle is defined as:

\begin{code}
c÷c : {τ : U} (c : τ ⟷ τ) → c ÷ c
c÷c {_} c < i , p , α > < j , q , β > =
  c ^ (i ℤ+ (ℤ- j)) ,
  α ● 2! (lower i (ℤ- j) ⊡ β ● assoc◎r ● id⇔ ⊡ (^⇔! j) ⊡ id⇔ ● id⇔ ⊡ rinv◎l ● idr◎l)
\end{code}

We can prove (see the accompanying code) that when applied to the same iterate (i.e. in
both argument positions), this will always return a combinator equivalent to the identity.
Thus such a function has no information content, and can be safely eliminated, which
is exactly what $\AgdaInductiveConstructor{ε-}$ does.  The interpreter then reads as

{\setlength{\mathindent}{0cm}
\medskip
{\footnotesize{
\begin{code}
𝓐𝓹 : {T₁ T₂ : U} → (T₁ ⟷ T₂) → Val T₁ → Val T₂
𝓐𝓹 (Prim x) v = prim x v
𝓐𝓹 id⟷ v = v 
𝓐𝓹 (c₁ ◎ c₂) v = let x = 𝓐𝓹 c₁ v in 𝓐𝓹 c₂ x
𝓐𝓹 (c₁ ⊕ c₂) (inl v) = inl (𝓐𝓹 c₁ v)
𝓐𝓹 (c₁ ⊕ c₂) (inr v) = inr (𝓐𝓹 c₂ v)
𝓐𝓹 (c₁ ⊗ c₂) [ v , w ] = [ 𝓐𝓹 c₁ v , 𝓐𝓹 c₂ w ]
𝓐𝓹 (η- c) ⋆ = tangl (c÷c c)
𝓐𝓹 (η+ c) ⋆ = tangr (c÷c c)
𝓐𝓹 (ε+ c) (tangr x) = ⋆
𝓐𝓹 (ε- c) (tangl x) = ⋆
𝓐𝓹 synchr⋆ [ tangr x , v ] = [ v , tangl x ]
𝓐𝓹 synchl⋆ [ v , tangl x ] = [ (tangr x) , v ]
\end{code}}}}


The two synchronization operations simply exchange the tangled product with an iterate.

In a similar vein, we can write an inverse interpreter.  We can then prove that these
interpreters are congruences for $≈$ (the equivalence on values).  We can further prove
that both are \emph{reversible}.  Furthermore, we can show two further coherence
conditions: first, that the reverse interpreter give equivalent results to the forward
interpreter applied to a reverse combinator, and second, that two equivalent combinators
(as given by a 2-combinator) will evaluate to equivalent values.

%%%%%%%
\subsection{Extensions}

We have a way to generate programs at run time from eta: it would be
nice to have a way to execute these programs.

name/coname; other diagrams from previous submission; ap; foldswap; other ideas

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

