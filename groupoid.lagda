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

open import Rational+ renaming (_+_ to _ℚ+_; _*_ to _ℚ*_)
  hiding (_≤_; _≤?_)
open import Data.Product using (Σ; Σ-syntax; _,_; ∃; ,_; _×_)

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
  _⇔_; 2!; id⇔; trans⇔; assoc◎l; assoc◎r; _⊡_;
  idl◎r; idl◎l; idr◎l; idr◎r;
  ⇔!; resp⊕⇔; resp⊗⇔; linv◎r; linv◎l; rinv◎l; rinv◎r)

infix 40 _^_ 

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Groupoids}
\label{sec:groupoids}

\amr{This section can focus on the categorical constructions. We can also do this without any Agda.} 

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

-- First each p is an Agda type
-- Perm p i is the type that contains the i^th iterate
-- of p, i.e p^i up to <=>.
-- the parens in the definition of ^ need to be there!

_^_ : {τ : FT} → (p : τ ⟷ τ) → (k : ℤ) → (τ ⟷ τ)
p ^ (+ 0) = id⟷
p ^ (+ (suc k)) = p ◎ (p ^ (+ k))
p ^ -[1+ 0 ] = ! p
p ^ (-[1+ (suc k) ]) = (! p) ◎ (p ^ -[1+ k ])

-- i.e. Perm is: for all i, any p' such that
-- p' ⇔ p ^ i

record Perm {τ : FT} (p : τ ⟷ τ) : Set where
  constructor perm
  field
    iter : ℤ
    p' : τ ⟷ τ
    p'⇔p^i : p' ⇔ p ^ iter
    
cong^ : {τ : FT} → {p q : τ ⟷ τ} → (k : ℤ) → (eq : p ⇔ q) →
  p ^ k ⇔ q ^ k
cong^ (+_ ℕ.zero) eq = id⇔
cong^ (+_ (suc n)) eq = eq ⊡ cong^ (+ n) eq
cong^ (-[1+_] ℕ.zero) eq = ⇔! eq
cong^ (-[1+_] (suc n)) eq = (⇔! eq) ⊡ cong^ (-[1+ n ]) eq

-- this should go into PiLevel1

!!⇔id : {t₁ t₂ : FT} → (p : t₁ ⟷ t₂) → p ⇔ ! (! p)
!!⇔id _⟷_.unite₊l = id⇔
!!⇔id _⟷_.uniti₊l = id⇔
!!⇔id _⟷_.unite₊r = id⇔
!!⇔id _⟷_.uniti₊r = id⇔
!!⇔id _⟷_.swap₊ = id⇔
!!⇔id _⟷_.assocl₊ = id⇔
!!⇔id _⟷_.assocr₊ = id⇔
!!⇔id _⟷_.unite⋆l = id⇔
!!⇔id _⟷_.uniti⋆l = id⇔
!!⇔id _⟷_.unite⋆r = id⇔
!!⇔id _⟷_.uniti⋆r = id⇔
!!⇔id _⟷_.swap⋆ = id⇔
!!⇔id _⟷_.assocl⋆ = id⇔
!!⇔id _⟷_.assocr⋆ = id⇔
!!⇔id _⟷_.absorbr = id⇔
!!⇔id _⟷_.absorbl = id⇔
!!⇔id _⟷_.factorzr = id⇔
!!⇔id _⟷_.factorzl = id⇔
!!⇔id _⟷_.dist = id⇔
!!⇔id _⟷_.factor = id⇔
!!⇔id _⟷_.distl = id⇔
!!⇔id _⟷_.factorl = id⇔
!!⇔id id⟷ = id⇔
!!⇔id (p ◎ q) = !!⇔id p ⊡ !!⇔id q
!!⇔id (p _⟷_.⊕ q) = resp⊕⇔ (!!⇔id p) (!!⇔id q)
!!⇔id (p _⟷_.⊗ q) = resp⊗⇔ (!!⇔id p) (!!⇔id q)

-- because ^ is iterated composition of the same thing,
-- then by associativity, we can hive off compositions
-- from left or right

assoc1 : {τ : FT} → {p : τ ⟷ τ} → (m : ℕ) →
  (p ◎ (p ^ (+ m))) ⇔ ((p ^ (+ m)) ◎ p)
assoc1 ℕ.zero = trans⇔ idr◎l idl◎r
assoc1 (suc m) = trans⇔ (id⇔ ⊡ assoc1 m) assoc◎l

assoc1- : {τ : FT} → {p : τ ⟷ τ} → (m : ℕ) →
  ((! p) ◎ (p ^ -[1+ m ])) ⇔ ((p ^ -[1+ m ]) ◎ (! p))
assoc1- ℕ.zero = id⇔
assoc1- (suc m) = trans⇔ (id⇔ ⊡ assoc1- m) assoc◎l

-- Property of ^: negating exponent is same as
-- composing in the other direction, then reversing.
^⇔! : {τ : FT} → {p : τ ⟷ τ} → (k : ℤ) →
  (p ^ (ℤ- k)) ⇔ ! (p ^ k)
^⇔! (+_ ℕ.zero) = id⇔
-- need to dig deeper, as we end up negating
^⇔! (+_ (suc ℕ.zero)) = idl◎r
^⇔! (+_ (suc (suc n))) = trans⇔ (assoc1- n) (^⇔! (+ suc n) ⊡ id⇔)
^⇔! {p = p} (-[1+_] ℕ.zero) = trans⇔ idr◎l (!!⇔id p)
^⇔! {p = p} (-[1+_] (suc n)) =
  trans⇔ (assoc1 (suc n)) ((^⇔! -[1+ n ]) ⊡ (!!⇔id p))

-- first match on m, n, then proof is purely PiLevel1
lower : {τ : FT} {p : τ ⟷ τ} (m n : ℤ) →
  p ^ (m ℤ+ n) ⇔ ((p ^ m) ◎ (p ^ n))
lower (+_ ℕ.zero) (+_ n) = idl◎r
lower (+_ ℕ.zero) (-[1+_] n) = idl◎r
lower (+_ (suc m)) (+_ n) =
  trans⇔ (id⇔ ⊡ lower (+ m) (+ n)) assoc◎l
lower {p = p} (+_ (suc m)) (-[1+_] ℕ.zero) = 
  trans⇔ idr◎r (trans⇔ (id⇔ ⊡ linv◎r) (
  trans⇔ assoc◎l (2! (assoc1 m) ⊡ id⇔)))  -- p ^ ((m + 1) -1)
lower (+_ (suc m)) (-[1+_] (suc n)) = -- p ^ ((m + 1) -(1+1+n)
  trans⇔ (lower (+ m) (-[1+ n ])) (
  trans⇔ ((trans⇔ idr◎r (id⇔ ⊡ linv◎r))  ⊡ id⇔) (
  trans⇔ assoc◎r (trans⇔ (id⇔ ⊡ assoc◎r) (
  trans⇔ assoc◎l (2! (assoc1 m) ⊡ id⇔))))) 
lower (-[1+_] m) (+_ ℕ.zero) = idr◎r
lower (-[1+_] ℕ.zero) (+_ (suc n)) = 2! (trans⇔ assoc◎l (
  trans⇔ (rinv◎l ⊡ id⇔) idl◎l))
lower (-[1+_] (suc m)) (+_ (suc n)) = -- p ^ (-(1+m) + (n+1))
  trans⇔ (lower (-[1+ m ]) (+ n)) (
    trans⇔ ((trans⇔ idr◎r (id⇔ ⊡ rinv◎r))  ⊡ id⇔) (
  trans⇔ assoc◎r (trans⇔ (id⇔ ⊡ assoc◎r) (
  trans⇔ assoc◎l ((2! (assoc1- m)) ⊡ id⇔)))))
lower (-[1+_] ℕ.zero) (-[1+_] n) = id⇔
lower (-[1+_] (suc m)) (-[1+_] n) = -- p ^ (-(1+1+m) - (1+n))
  trans⇔ (id⇔ ⊡ lower (-[1+ m ]) (-[1+ n ])) assoc◎l


-- orderC is the groupoid with objects p^i

orderC : {τ : FT} → (p : τ ⟷ τ) → Category _ _ _
orderC {τ} p = record {
     Obj = Perm p
   ; _⇒_ = λ { (perm i p₁ _) (perm j p₂ _) → p₁ ⇔ p₂ } 
   ; _≡_ = λ _ _ → ⊤ 
   ; id = id⇔ 
   ; _∘_ = λ α β → trans⇔ β α
   ; assoc = tt
   ; identityˡ = tt
   ; identityʳ = tt 
   ; equiv = record { refl = tt; sym = λ _ → tt; trans = λ _ _ → tt }
   ; ∘-resp-≡ = λ _ _ → tt  
   }
   where open Perm
   
orderG : {τ : FT} → (p : τ ⟷ τ) → Groupoid (orderC p)
orderG {τ} p = record {
    _⁻¹ = 2!
  ; iso = record {
        isoˡ = tt
      ; isoʳ = tt
      }
  }

-- discrete groupoids corresponding to plain pi types

discreteC : Set → Category _ _ _
discreteC S = record {
     Obj = S
    ; _⇒_ = _≡_
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

-- fractional groupoid

1/orderC : {τ : FT} (p : τ ⟷ τ) → Category _ _ _
1/orderC {τ} pp = record {
     Obj = ⊤
    ; _⇒_ = λ _ _ → Perm pp
    ; _≡_ = λ { (perm m p _) (perm n q  _) → p ⇔ q } -- pp ^ m ⇔ pp ^ n 
    ; id = perm (+ 0) id⟷ id⇔
    ; _∘_ = λ { (perm m p α) (perm n q β) →
        perm (m ℤ+ n) (p ◎ q) (trans⇔ (α ⊡ β) (2! (lower m n))) }
    ; assoc = assoc◎r
    ; identityˡ = idl◎l
    ; identityʳ =  idr◎l
    ; equiv = record { refl = id⇔; sym = 2!; trans = trans⇔ }
    ; ∘-resp-≡ = _⊡_
    }

1/orderG : {τ : FT} (p : τ ⟷ τ) → Groupoid (1/orderC p)
1/orderG p = record {
      _⁻¹ = λ { (perm i q eq) →
              perm (ℤ- i) (! q) (trans⇔ (⇔! eq) (2! (^⇔! {p = p} i)))}
    ; iso = record { isoˡ = rinv◎l ; isoʳ = linv◎l }
    }
\end{code}

%% _//_ : (τ : FT) → (p : τ ⟷ τ) → Category _ _ _
%% τ // p = Product (discreteC (El τ)) (1/orderC p)
%%   where open Universe.Universe UFT
%% 
%% quotientG : (τ : FT) → (p : τ ⟷ τ) → Groupoid (τ // p)
%% quotientG = {!!} 

So now we can finally define our denotations:

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

Define action groupoids $\ag{\tau}{p}$ and show they are equivalent to
uparrow tau times 1 over hash p

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

% -- These are true, but no longer used
% -- cancel-rinv : {τ : FT} → {p : τ ⟷ τ} → (i : ℤ) →
% --   ((p ^ i) ◎ ((! p) ^ i)) ⇔ id⟷
% -- cancel-rinv (+_ ℕ.zero) = idl◎l
% -- cancel-rinv (+_ (suc n)) = 
% --   trans⇔ (assoc1 n ⊡ id⇔) (trans⇔ assoc◎l (trans⇔ (assoc◎r ⊡ id⇔)
% --   (trans⇔ ((id⇔ ⊡ linv◎l) ⊡ id⇔) (trans⇔ (idr◎l ⊡ id⇔) (
% --   cancel-rinv (+ n))))))
% -- cancel-rinv (-[1+_] ℕ.zero) = linv◎l
% -- cancel-rinv (-[1+_] (suc n)) = 
% --   trans⇔ (assoc1- n ⊡ id⇔) (
% --   trans⇔ assoc◎l (trans⇔ (assoc◎r ⊡ id⇔)
% --   (trans⇔ ((id⇔ ⊡ linv◎l) ⊡ id⇔) (trans⇔ (idr◎l ⊡ id⇔)
% --   (cancel-rinv -[1+ n ])))))

% -- cancel-linv : {τ : FT} → {p : τ ⟷ τ} → (i : ℤ) →
% --   (((! p) ^ i) ◎ (p ^ i)) ⇔ id⟷
% -- cancel-linv (+_ ℕ.zero) = idr◎l
% -- cancel-linv (+_ (suc n)) = trans⇔ (assoc1 n ⊡ id⇔) (
% --    trans⇔ assoc◎l (trans⇔ (assoc◎r ⊡ id⇔) (
% --    trans⇔ ((id⇔ ⊡ rinv◎l) ⊡ id⇔) (trans⇔ (idr◎l ⊡ id⇔)
% --    (cancel-linv (+ n))))))
% -- cancel-linv (-[1+_] ℕ.zero) = rinv◎l
% -- cancel-linv (-[1+_] (suc n)) = trans⇔ (assoc1- n ⊡ id⇔) (
% --   trans⇔  assoc◎l (trans⇔ (assoc◎r ⊡ id⇔) (
% --   trans⇔ ((id⇔ ⊡ rinv◎l) ⊡ id⇔) (trans⇔ (idr◎l ⊡ id⇔) (
% --   cancel-linv -[1+ n ])))))

