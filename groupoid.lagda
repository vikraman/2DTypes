\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module groupoid where

open import Level using () renaming (zero to l0; suc to lsuc)

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; suc)
open import Data.Integer
  using (ℤ; +_; -[1+_])
  renaming (-_ to ℤ-; suc to ℤsuc; _+_ to _ℤ+_)
open import Algebra using (CommutativeMonoid)
open import Algebra.Structures using (IsCommutativeMonoid; IsSemigroup)
import Data.Integer.Addition.Properties as Add
open CommutativeMonoid Add.commutativeMonoid
  using ()
  renaming (isCommutativeMonoid to ℤ+-isCommutativeMonoid;
            identityˡ to ℤ+-identityˡ)
open IsCommutativeMonoid ℤ+-isCommutativeMonoid
  using ()
  renaming (isSemigroup to ℤ+-isSemigroup;
            comm to ℤ+-comm)
open IsSemigroup ℤ+-isSemigroup
  using ()
  renaming (assoc to ℤ+-assoc)

open import Rational+ renaming (_+_ to _ℚ+_; _*_ to _ℚ*_)
  hiding (_≤_; _≤?_)
open import Data.Product using (Σ; Σ-syntax; _,_; ∃; ,_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)
open import Universe using (Universe)

open import Categories.Category using (Category)
open import Categories.Product using (Product)
open import Categories.Groupoid using (Groupoid)
open import Categories.Groupoid.Sum using () renaming (Sum to GSum)
open import Categories.Groupoid using () renaming (Product to GProduct)
-- open import Categories.Monad using (Monad)
-- open import Comonad using (Comonad)

open import pibackground using (FT; UFT; ∣_∣; order; order-nz; 
  _⟷_; !; id⟷; _◎_;
  _⇔_; 2!; id⇔; trans⇔; assoc◎l; idr◎l; idl◎l; _⊡_)

infix 40 _^_ 

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Groupoids}
\label{sec:groupoids}

%%%%%
\subsection{A Universe of Groupoids} 

\begin{code}
data FT/ : Set where
  ⇑    : FT → FT/
  #    : {τ : FT} → (p : τ ⟷ τ) → FT/ 
  1/#  : {τ : FT} → (p : τ ⟷ τ) → FT/
  _⊞_  : FT/ → FT/ → FT/              
  _⊠_  : FT/ → FT/ → FT/

UG : Universe l0 (lsuc l0)
UG = record {
    U = FT/
 ;  El = λ T → Σ[ ℂ ∈ Category l0 l0 l0 ] (Groupoid ℂ)
 }

card : FT/ → ℚ
card (⇑ τ)      = mkRational ∣ τ ∣ 1 {tt}
card (# p)      = mkRational (order p) 1 {tt}
card (1/# p)    = mkRational 1 (order p) {order-nz}
card (T₁ ⊞ T₂)  = (card T₁) ℚ+ (card T₂)
card (T₁ ⊠ T₂)  = (card T₁) ℚ* (card T₂)
\end{code}

%%%%%
\subsection{Groupoids from $\Pi$-Combinators} 

The goal is to define a function that takes a $T$ in $FT/$ and
produces something of type $Universe.El~UG~T$, i.e., a particular
groupoid.

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

^⇔ : {τ : FT} {p : τ ⟷ τ} {i j : ℤ} → i ≡ j → p ^ i ⇔ p ^ j
^⇔ (refl) = id⇔

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

1/orderC : {τ : FT} (p : τ ⟷ τ) → Category _ _ _
1/orderC {τ} p = record {
     Obj = ⊤
    ; _⇒_ = λ _ _ → Σ[ i ∈ ℤ ] (Perm p i)
    ; _≡_ = λ { (m , (p₁ , _)) (n , (p₂ , _)) → p₁ ^ m ⇔ p₂ ^ n}
    ; id = (+ 0 , singleton id⟷)
    ; _∘_ = λ { (m , (p₁ , α)) (n , (p₂ , β)) → ((m ℤ+ n) , (p , id⇔)) }
    ; assoc = λ { {f = (m₁ , (p₁ , α₁))} {g = (m₂ , (p₂ , α₂))} {h = (m₃ , (p₃ , α₃))}
                → ^⇔ (ℤ+-assoc m₃ m₂ m₁)} -- assoc◎l
    ; identityˡ = λ { {f = (m , (p₁ , α))}
                    → 2! (trans⇔ α (^⇔ (sym (ℤ+-identityˡ m)))) } -- idr◎l 
    ; identityʳ = λ { {f = (m , (p₁ , α))}
                    → 2! (trans⇔ α (^⇔ (sym (trans (ℤ+-comm m (+ 0)) (ℤ+-identityˡ m))))) } -- idl◎l
    ; equiv = record { refl = id⇔; sym = 2!; trans = trans⇔ }
    ; ∘-resp-≡ = λ { {f = (m₁ , (p₁ , α₁))} {h = (m₂ , (p₂ , α₂))}
                     {g = (m₃ , (p₃ , α₃))} {i = (m₄ , (p₄ , α₄))} α β
                   → {!!}} -- β ⊡ α
    }

1/orderG : {τ : FT} (p : τ ⟷ τ) → Groupoid (1/orderC p)
1/orderG = {!!} 

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

-- _//_ : (τ : FT) → (p : τ ⟷ τ) → Category _ _ _
-- τ // p = Product (discreteC (El τ)) (1/orderC p)
--   where open Universe.Universe UFT

-- quotientG : (τ : FT) → (p : τ ⟷ τ) → Groupoid (τ // p)
-- quotientG = {!!} 

\end{code}

\begin{code}
⟦_⟧/ : (T : FT/) → Universe.El UG T
⟦ ⇑ S ⟧/ = , discreteG (Universe.El UFT S)
⟦ # p ⟧/ = , orderG p
⟦ 1/# p ⟧/ = , 1/orderG p
⟦ T₁ ⊞ T₂ ⟧/ with ⟦ T₁ ⟧/ | ⟦ T₂ ⟧/
... | (_ , G₁) | (_ , G₂) = , GSum G₁ G₂
⟦ T₁ ⊠ T₂ ⟧/ with ⟦ T₁ ⟧/ | ⟦ T₂ ⟧/
... | (_ , G₁) | (_ , G₂) = , GProduct G₁ G₂
\end{code}

%%%%%
\subsection{Information Equivalence}
 
We need to show coherence of the definition of cardinalities on the
universe syntax with the Euler characteric of the category which in
our case also corresponds to the groupoid cardinality. There are
several formulations and explanations. The following is quite simple
to implement: first collapse all the isomorphic objects. Then fix a
particular order of the objects and write a matrix whose $ij$'s entry
is the number of morphisms from $i$ to $j$. Invert the matrix. The
cardinality is the sum of the elements in the matrix.

Our notion of information equivalence is coarser than the conventional
notion of equivalence of categories (groupoids). This is fine as there
are several competing notions of equivalence of groupoids that are
coarser than strict categorical equivalence. 

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
particular categories in question are equivalent. 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% -- p is a monad on (order p)

% ^suc : {τ : FT} {p : τ ⟷ τ} {i : ℤ} → p ^ ℤsuc i ⇔ p ◎ p ^ i
% ^suc = {!!}

% ^resp : {τ : FT} {p q : τ ⟷ τ} {i : ℤ} → (q ^ i ⇔ p ^ i) → (q ◎ q ^ i ⇔ p ◎ p ^ i)
% ^resp = {!!} 

% orderM : {τ : FT} → (p : τ ⟷ τ) → Monad (orderC p)
% orderM {τ} p = record {
%     F = record {
%           F₀ = λ { (i , (q , α)) →
%                  (ℤsuc i , (q , trans⇔ (^suc {p = q} {i = i})
%                                 (trans⇔ (^resp {p = p} {q = q} {i = i} α)
%                                 (2! (^suc {p = p} {i = i})))))}
%         ; F₁ = {!!}
%         }
%   ; η = record {
%           η = {!!}
%         ; commute = λ _ → tt
%         }
%   ; μ = record {
%           η = {!!}
%         ; commute = λ _ → tt
%         }
%   ; assoc = tt
%   ; identityˡ = tt
%   ; identityʳ = tt
%   }

% -- ! p is a comonad on (order p)

% orderCom : {τ : FT} → (p : τ ⟷ τ) → Comonad (orderC p)
% orderCom {τ} p = record {
%     F = record {
%           F₀ = {!!} 
%         ; F₁ = {!!}
%         }
%   ; η = record {
%           η = {!!}
%         ; commute = λ _ → tt
%         }
%   ; μ = record {
%           η = {!!}
%         ; commute = λ _ → tt
%         }
%   ; assoc = tt
%   ; identityˡ = tt
%   ; identityʳ = tt
%   }

% -- the monad and comonad are inverses
% -- idea regarding the significance of the
% -- monad/comonad construction. Say we have
% -- a combinator c : #p ⟷ #q that maps
% -- p^i to q^j. Then we can use the q-monad
% -- to write a combinator pc : #p ⟷ #q which
% -- maps p^i to q^j using c and then to
% -- q^(suc j) using the monad. We can use
% -- the comonad to map p^i to p^(suc i) and
% -- then to #q using c. So as an effect we can
% -- constuct maps that move around #p and #q
% -- using p and q.
% --
% -- A more general perspective: computations
% -- happen in a context in the following sense:
% -- say we have a collection of values v1, v2, ...
% -- a computation takes vi to wi. In many cases,
% -- the vi's form a structure of some kind and
% -- so do the wi's. A monad focuses on the w's
% -- structure and how to compose computations
% -- on it. The comonad focuses on the v's structure
% -- and how to compose computations on it. Some
% -- people talk about monads expressing how to
% -- affect the context and comonads expressing
% -- what to expect from the context. 

% -- moncom = ?

% -- 1/orderC is the the groupoid with one object
% --   and morphisms p^i

% 1/orderM : {τ : FT} (p : τ ⟷ τ) → Monad (1/orderC p)
% 1/orderM = {!!} 

% 1/orderCom : {τ : FT} (p : τ ⟷ τ) → Comonad (1/orderC p)
% 1/orderCom = {!!} 

% The definition of $p$ will induce three types (groupoids):

% \begin{itemize}

% \item The first is the action groupoid $\ag{C}{p}$ depicted below. The
% objects are the elements of $C$ and there is a morphism between $x$
% and $y$ iff $p^k$ for some $k$ maps $x$ to $y$. We do not draw the
% identity morphisms. Note that all of $p^0$, $p^1$, and $p^2$ map
% \texttt{sat} to \texttt{sat} which explains the two non-trivial
% morphisms on \texttt{sat}:

% \begin{center}
% \begin{tikzpicture}[scale=0.4,every node/.style={scale=0.4}]
%   \draw (0,0) ellipse (8cm and 1.6cm);
%   \node[below] at (-6,0) {\texttt{sun}};
%   \node[below] at (-4,0) {\texttt{mon}};
%   \node[below] at (-2,0) {\texttt{tue}};
%   \node[below] at (0,0) {\texttt{wed}};
%   \node[below] at (2,0) {\texttt{thu}};
%   \node[below] at (4,0) {\texttt{fri}};
%   \node[below] (B) at (6,0) {\texttt{sat}};
%   \draw[fill] (-6,0) circle [radius=0.05];
%   \draw[fill] (-4,0) circle [radius=0.05];
%   \draw[fill] (-2,0) circle [radius=0.05];
%   \draw[fill] (0,0) circle [radius=0.05];
%   \draw[fill] (2,0) circle [radius=0.05];
%   \draw[fill] (4,0) circle [radius=0.05];
%   \draw[fill] (6,0) circle [radius=0.05];
%   \draw (-6,0) -- (-4,0);
%   \draw (-4,0) -- (-2,0);
%   \draw (0,0) -- (2,0);
%   \draw (2,0) -- (4,0);
%   \draw (-6,0) to[bend left] (-2,0) ;
%   \draw (0,0) to[bend left] (4,0) ;
%   \path (B) edge [loop above, looseness=3, in=48, out=132] node[above] {} (B);
%   \path (B) edge [loop above, looseness=5, in=40, out=140] node[above] {} (B);
% \end{tikzpicture}
% \end{center}

% To calculate the cardinality, we first collapse all the isomorphic
% objects (i.e., collapse the two strongly connected components to one
% object each) and write the resulting matrix:
% \[
% \begin{pmatrix}
% 1 & 0 & 0 \\
% 0 & 1 & 0 \\
% 0 & 0 & 3 
% \end{pmatrix}
% \]
% Its inverse is 0 everywhere except on the main diagonal which has
% entries 1, 1, and $\frac{1}{3}$ and hence the cardinality of this
% category is $2\frac{1}{3}$.

% \item The second which we call $1/p$ is depicted below. It has one
% trivial object and a morphism for each iteration of $p$. It has
% cardinality $\frac{1}{3}$ as the connectivity matrix has one entry
% $3$ whose inverse is $\frac{1}{3}$:

% \begin{center}
% \begin{tikzpicture}[scale=0.7,every node/.style={scale=0.8}]
%   \draw (0,1.4) ellipse (2cm and 2cm);
%   \node[below] (B) at (0,0) {\texttt{*}};
% %%  \path (B) edge [loop above] node[above] {$p^0$} (B);
%   \path (B) edge [loop above, looseness=15, in=48, out=132] node[above] {$p$} (B);
%   \path (B) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (B);
% \end{tikzpicture}
% \end{center}

% \item The third is the order type $\order{p}$ depicted below. It has
% three objects corresponding to each iteration of $p$. It has
% cardinality $3$:
% \begin{center}
% \begin{tikzpicture}[scale=0.7,every node/.style={scale=0.8}]
%   \draw (0,0) ellipse (4cm and 1cm);
%   \node[below] at (-2,0) {$p^0$};
%   \node[below] at (0,0) {$p^1$};
%   \node[below] at (2,0) {$p^2$};
%   \draw[fill] (-2,0) circle [radius=0.05];
%   \draw[fill] (0,0) circle [radius=0.05];
%   \draw[fill] (2,0) circle [radius=0.05];
% \end{tikzpicture}
% \end{center}
% \end{itemize}

% Each combinator $p : \tau ⟷ \tau$ will give rise to two groupoids:
% \begin{itemize}
% \item one groupoid $\mathit{order}~p$ with objects $p^i$ and morphisms $⇔$, and 
% \item another groupoid $\mathit{1/order}~p$ with one object and morphisms $p^i$ under $⇔$
% \end{itemize}
% There is also a third groupoid $\ag{\tau}{p}$ that is equivalent to
% $\tau \boxtimes \mathit{1/order}~p$ and that is a conventional quotient type.

% Is weak equivalence in HoTT related??? Here is one definition: A map
% $f : X \rightarrow Y$ is a weak homotopy equivalence (or just a weak
% equivalence) if for every $x \in X$, and all $n \geq 0$ the map
% $\pi_n(X,x) \rightarrow \pi_n(Y,f(x))$ is a bijection. In our setting
% this might mean something like: two types $T$ and $U$ are equivalent
% if $T \leftrightarrow T$ is equivalent to $U \leftrightarrow U$ are
% equivalent.

