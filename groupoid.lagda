\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module groupoid where

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; suc)
open import Data.Integer
  using (ℤ; +_; -[1+_])
  renaming (-_ to ℤ-; suc to ℤsuc; _+_ to _ℤ+_)
open import Data.Product using (Σ; Σ-syntax; _,_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
open import Universe using (Universe)

open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Categories.Monad using (Monad)
open import Comonad using (Comonad)

open import Categories.Product using (Product)

open import pibackground using (FT; UFT; 
  _⟷_; !; id⟷; _◎_;
  _⇔_; 2!; id⇔; trans⇔; assoc◎l; idr◎l; idl◎l; _⊡_)

infix 40 _^_ 

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Combinators as Groupoids}

We will decompose the type $C$ into the products of $A$ and $B$ where
$A$ will have cardinality $2\frac{1}{3}$ and $B$ will cardinality
3. The first step is to explain how to calculate such
cardinalities. We will use the Euler characteristic of a category
which in our case also correspond to the groupoid cardinality. There
are several formulations and explanations. The following is quite
simple to implement: first collapse all the isomorphic objects. Then
fix a particular order of the objects and write a matrix whose $ij$'s
entry is the number of morphisms from $i$ to $j$. Invert the
matrix. The cardinality is the sum of the elements in the matrix.

The definition of $p$ will induce three types (groupoids):

\begin{itemize}

\item The first is the action groupoid $\ag{C}{p}$ depicted below. The
objects are the elements of $C$ and there is a morphism between $x$
and $y$ iff $p^k$ for some $k$ maps $x$ to $y$. We do not draw the
identity morphisms. Note that all of $p^0$, $p^1$, and $p^2$ map
\texttt{sat} to \texttt{sat} which explains the two non-trivial
morphisms on \texttt{sat}:

\begin{center}
\begin{tikzpicture}[scale=0.4,every node/.style={scale=0.4}]
  \draw (0,0) ellipse (8cm and 1.6cm);
  \node[below] at (-6,0) {\texttt{sun}};
  \node[below] at (-4,0) {\texttt{mon}};
  \node[below] at (-2,0) {\texttt{tue}};
  \node[below] at (0,0) {\texttt{wed}};
  \node[below] at (2,0) {\texttt{thu}};
  \node[below] at (4,0) {\texttt{fri}};
  \node[below] (B) at (6,0) {\texttt{sat}};
  \draw[fill] (-6,0) circle [radius=0.05];
  \draw[fill] (-4,0) circle [radius=0.05];
  \draw[fill] (-2,0) circle [radius=0.05];
  \draw[fill] (0,0) circle [radius=0.05];
  \draw[fill] (2,0) circle [radius=0.05];
  \draw[fill] (4,0) circle [radius=0.05];
  \draw[fill] (6,0) circle [radius=0.05];
  \draw (-6,0) -- (-4,0);
  \draw (-4,0) -- (-2,0);
  \draw (0,0) -- (2,0);
  \draw (2,0) -- (4,0);
  \draw (-6,0) to[bend left] (-2,0) ;
  \draw (0,0) to[bend left] (4,0) ;
  \path (B) edge [loop above, looseness=3, in=48, out=132] node[above] {} (B);
  \path (B) edge [loop above, looseness=5, in=40, out=140] node[above] {} (B);
\end{tikzpicture}
\end{center}

To calculate the cardinality, we first collapse all the isomorphic
objects (i.e., collapse the two strongly connected components to one
object each) and write the resulting matrix:
\[
\begin{pmatrix}
1 & 0 & 0 \\
0 & 1 & 0 \\
0 & 0 & 3 
\end{pmatrix}
\]
Its inverse is 0 everywhere except on the main diagonal which has
entries 1, 1, and $\frac{1}{3}$ and hence the cardinality of this
category is $2\frac{1}{3}$.

\item The second which we call $1/p$ is depicted below. It has one
trivial object and a morphism for each iteration of $p$. It has
cardinality $\frac{1}{3}$ as the connectivity matrix has one entry
$3$ whose inverse is $\frac{1}{3}$:

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.8}]
  \draw (0,1.4) ellipse (2cm and 2cm);
  \node[below] (B) at (0,0) {\texttt{*}};
%%  \path (B) edge [loop above] node[above] {$p^0$} (B);
  \path (B) edge [loop above, looseness=15, in=48, out=132] node[above] {$p$} (B);
  \path (B) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (B);
\end{tikzpicture}
\end{center}

\item The third is the order type $\order{p}$ depicted below. It has
three objects corresponding to each iteration of $p$. It has
cardinality $3$:
\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.8}]
  \draw (0,0) ellipse (4cm and 1cm);
  \node[below] at (-2,0) {$p^0$};
  \node[below] at (0,0) {$p^1$};
  \node[below] at (2,0) {$p^2$};
  \draw[fill] (-2,0) circle [radius=0.05];
  \draw[fill] (0,0) circle [radius=0.05];
  \draw[fill] (2,0) circle [radius=0.05];
\end{tikzpicture}
\end{center}
\end{itemize}

Each combinator $p : \tau ⟷ \tau$ will give rise to two groupoids:
\begin{itemize}
\item one groupoid $\mathit{order}~p$ with objects $p^i$ and morphisms $⇔$, and 
\item another groupoid $\mathit{1/order}~p$ with one object and morphisms $p^i$ under $⇔$
\end{itemize}
There is also a third groupoid $\ag{\tau}{p}$ that is equivalent to
$\tau \boxtimes \mathit{1/order}~p$ and that is a conventional quotient type.

\begin{code}

-- First each p^i is an Agda type
-- Perm p i is the singleton type that only
--   contains p^i up to ⇔ 

_^_ : {τ : FT} → (p : τ ⟷ τ) → (k : ℤ) → (τ ⟷ τ)
p ^ (+ 0) = id⟷
p ^ (+ (suc k)) = p ◎ p ^ (+ k)
p ^ -[1+ 0 ] = ! p
p ^ (-[1+ (suc k) ]) = ! p ◎ p ^ -[1+ k ]

Perm : {τ : FT} → (p : τ ⟷ τ) (i : ℤ) → Set
Perm {τ} p i = Σ[ p' ∈ (τ ⟷ τ) ] (p' ^ i ⇔ p ^ i)

singleton : {τ : FT} → (p : τ ⟷ τ) → Perm p (+ 1)
singleton p = (p , id⇔)

-- orderC is the groupoid with objects p^i

orderC : {τ : FT} → (p : τ ⟷ τ) → Category _ _ _
orderC {τ} p = record {
     Obj = Σ[ i ∈ ℤ ] (Perm p i)
   ; _⇒_ = λ { (m , (p , _)) (n , (q , _)) → p ^ m ⇔ q ^ n } 
   ; _≡_ = λ _ _ → ⊤ 
   ; id = id⇔ 
   ; _∘_ = λ α β → trans⇔ β α
   ; assoc = tt
   ; identityˡ = tt
   ; identityʳ = tt 
   ; equiv = record { refl = tt; sym = λ _ → tt; trans = λ _ _ → tt }
   ; ∘-resp-≡ = λ _ _ → tt  
   }

orderG : {τ : FT} → (p : τ ⟷ τ) → Groupoid (orderC p)
orderG {τ} p = record {
    _⁻¹ = 2!
  ; iso = record {
        isoˡ = tt
      ; isoʳ = tt
      }
  }

-- p is a monad on (order p)

^suc : {τ : FT} {p : τ ⟷ τ} {i : ℤ} → p ^ ℤsuc i ⇔ p ◎ p ^ i
^suc = {!!}

^resp : {τ : FT} {p q : τ ⟷ τ} {i : ℤ} → (q ^ i ⇔ p ^ i) → (q ◎ q ^ i ⇔ p ◎ p ^ i)
^resp = {!!} 

orderM : {τ : FT} → (p : τ ⟷ τ) → Monad (orderC p)
orderM {τ} p = record {
    F = record {
          F₀ = λ { (i , (q , α)) →
                 (ℤsuc i , (q , trans⇔ (^suc {p = q} {i = i})
                                (trans⇔ (^resp {p = p} {q = q} {i = i} α)
                                (2! (^suc {p = p} {i = i})))))}
        ; F₁ = {!!}
        }
  ; η = record {
          η = {!!}
        ; commute = λ _ → tt
        }
  ; μ = record {
          η = {!!}
        ; commute = λ _ → tt
        }
  ; assoc = tt
  ; identityˡ = tt
  ; identityʳ = tt
  }

-- ! p is a comonad on (order p)

orderCom : {τ : FT} → (p : τ ⟷ τ) → Comonad (orderC p)
orderCom {τ} p = record {
    F = record {
          F₀ = {!!} 
        ; F₁ = {!!}
        }
  ; η = record {
          η = {!!}
        ; commute = λ _ → tt
        }
  ; μ = record {
          η = {!!}
        ; commute = λ _ → tt
        }
  ; assoc = tt
  ; identityˡ = tt
  ; identityʳ = tt
  }

-- the monad and comonad are inverses
-- idea regarding the significance of the
-- monad/comonad construction. Say we have
-- a combinator c : #p ⟷ #q that maps
-- p^i to q^j. Then we can use the q-monad
-- to write a combinator pc : #p ⟷ #q which
-- maps p^i to q^j using c and then to
-- q^(suc j) using the monad. We can use
-- the comonad to map p^i to p^(suc i) and
-- then to #q using c. So as an effect we can
-- constuct maps that move around #p and #q
-- using p and q.
--
-- A more general perspective: computations
-- happen in a context in the following sense:
-- say we have a collection of values v1, v2, ...
-- a computation takes vi to wi. In many cases,
-- the vi's form a structure of some kind and
-- so do the wi's. A monad focuses on the w's
-- structure and how to compose computations
-- on it. The comonad focuses on the v's structure
-- and how to compose computations on it. Some
-- people talk about monads expressing how to
-- affect the context and comonads expressing
-- what to expect from the context. 

-- moncom = ?

-- 1/orderC is the the groupoid with one object
--   and morphisms p^i

1/orderC : {τ : FT} (p : τ ⟷ τ) → Category _ _ _
1/orderC {τ} p = record {
     Obj = ⊤
    ; _⇒_ = λ _ _ → Σ[ i ∈ ℤ ] (Perm p i)
    ; _≡_ = λ { (m , (p , _)) (n , (q , _)) → p ^ m ⇔ q ^ n} 
    ; id = (+ 0 , singleton id⟷)
    ; _∘_ = λ { (m , (p , α)) (n , (q , β)) → (m ℤ+ n , (p ◎ q , {!!})) }
    ; assoc = {!!} -- assoc◎l 
    ; identityˡ = {!!} -- idr◎l 
    ; identityʳ = {!◎l !} -- idl◎l
    ; equiv = record { refl = id⇔; sym = 2!; trans = trans⇔ }
    ; ∘-resp-≡ = λ α β → {!!} -- β ⊡ α
    }


1/orderG : {τ : FT} (p : τ ⟷ τ) → Groupoid (1/orderC p)
1/orderG = {!!} 

1/orderM : {τ : FT} (p : τ ⟷ τ) → Monad (1/orderC p)
1/orderM = {!!} 

1/orderCom : {τ : FT} (p : τ ⟷ τ) → Comonad (1/orderC p)
1/orderCom = {!!} 

-- τ // p

discreteC : Set → Category _ _ _
discreteC S = record {
     Obj = S
    ; _⇒_ = λ s₁ s₂ → s₁ ≡ s₂
    ; _≡_ = λ _ _ → ⊤ 
    ; id = refl 
    ; _∘_ = λ { {A} {.A} {.A} refl refl → refl }
    ; assoc = tt 
    ; identityˡ = tt 
    ; identityʳ = tt 
    ; equiv = record { refl = tt; sym = λ _ → tt; trans = λ _ _ → tt }  
    ; ∘-resp-≡ = λ _ _ → tt 
    }

discreteG : (S : Set) → Groupoid (discreteC S)
discreteG S = record
  { _⁻¹ = λ { {A} {.A} refl → refl }
  ; iso = record { isoˡ = tt; isoʳ = tt }
  }

_//_ : (τ : FT) → (p : τ ⟷ τ) → Category _ _ _
τ // p = Product (discreteC (El τ)) (1/orderC p)
  where open Universe.Universe UFT

quotientG : (τ : FT) → (p : τ ⟷ τ) → Groupoid (τ // p)
quotientG = {!!} 

\end{code}

%%%%%
\subsection{Information Equivalence}
 
Our notion of information equivalence is coarser than the conventional
notion of equivalence of categories (groupoids). This is fine as there
are several competing notions of equivalence of groupoids that are
coarser than strict categorical equivalence. 

Need to explain the example above in terms of information!!! The best
explanation I have so far is the credit card analogy: we want money
here and now, so we create money and a debt. That debt is reconciled
somewhere else. The example above uses the same: we want to process
some values from $C$ here and now. So we create a third of them,
process them, and reconcile this third somewhere else. When all three
thirds have been reconciled the computation is finished. 

There are however other notions of equivalence of groupoids like
Morita equivalence and weak equivalence that we explore later. The
intuition of these weaker notions of equivalence is that two groupoids
can be considered equivalent if it is not possible to distinguish them
using certain observations. This informally corresponds to the notion
of ``observational equivalence'' in programming language
semantics. Note that negative entropy can only make sense locally in
an open system but that in a closed system, i.e., in a complete
computation, entropy cannot be negative. Thus we restrict
observational contexts to those in which fractional types do not
occur. Note that two categories can have the same cardinality but not
be equivalent or even Morita equivalent but the converse is
guaranteed. So it is necessary to have a separate notion of
equivalence and check that whenever we have the same cardinality, the
particular categories in question are equivalent. The second
equivalence, that $C \boxtimes 1/p$ is equivalent to $\ag{C}{p}$ would
follow from two facts: that three copies of $1/p$ simplify to a point
(which is the first equivalence above) and that three connected points
also simplify to a single point (which is relatively easy to
establish).

Is weak equivalence in HoTT related??? Here is one definition: A map
$f : X \rightarrow Y$ is a weak homotopy equivalence (or just a weak
equivalence) if for every $x \in X$, and all $n \geq 0$ the map
$\pi_n(X,x) \rightarrow \pi_n(Y,f(x))$ is a bijection. In our setting
this might mean something like: two types $T$ and $U$ are equivalent
if $T \leftrightarrow T$ is equivalent to $U \leftrightarrow U$ are
equivalent.

First the equivalence can only make sense in a framework where
everything is reversible. If we allow arbitrary functions then bad
things happen as we can throw away the negative information for
example. In our reversible information-preserving framework, the
theory is consistent in the sense that not all types are
identified. This is easy to see as we only identify types that have
the same cardinality. This is evident for all the combinators except
for the new ones. For those new ones the only subtle situation is with
the empty type. Note however that there is no way to define 1/0 and no
permutation has order 0. For 0 we have one permutation id which has
order 1. So if we try to use it, we will map 1 to 1 times 1/id which
is fine. So if we always preserve types and trivially 1 and 0 have
different cardinalities so there is no way to identify them and we are
consistent.

"apply this program i times" is a VALUE !!!

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

