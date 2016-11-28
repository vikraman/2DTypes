\appendix
\section{Agda Construction of Groupoids}

\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module appendix where

open import 2D.Types

open import Data.Sum
open import Data.Product hiding (<_,_>;,_)
open import Data.Empty
open import Data.Unit

open import Categories.Category
import Categories.Product as C
import Categories.Coproduct as C
open import Categories.Groupoid
import Categories.Groupoid.Product as G
import Categories.Groupoid.Coproduct as G
open import Level hiding (lower)

open import Relation.Binary.PropositionalEquality
open import Function
open import 2D.Power
open import 2D.Iter
open import 2D.ProgMorphisms

open import Data.Integer as ℤ hiding (∣_∣)

discreteC : Set → Category zero zero zero
discreteC S = record {
    Obj = S
  ; _⇒_ = _≡_
  ; _≡_ = λ _ _ → ⊤
  ; id = refl
  ; _∘_ = flip trans
  ; assoc = tt
  ; identityˡ = tt
  ; identityʳ = tt
  ; equiv = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
  ; ∘-resp-≡ = λ _ _ → tt
  }

discreteG : (S : Set) → Groupoid (discreteC S)
discreteG S = record { _⁻¹ = sym
                     ; iso = record { isoˡ = tt ; isoʳ = tt }
                     }
\end{code}
}

First, the iteration groupoids, corresponding to $\order{p}$.
Then we present a hand-unrolled version which corresponds to
$\iorder{p}$. And finally the general case of $\div{p}{q}$.
The reader might find it an interesting exercise to show
that the groupoids do indeed degenerate correctly when
$p$ or $q$ is chosen as the identity combinator.

{\setlength{\mathindent}{0cm}
\medskip
{\footnotesize{
\begin{code}

iterationC : {τ : U} → (p : τ ⟷ τ) → Category _ _ _
iterationC {τ} p = record {
     Obj = Iter p
  ;  _⇒_ = λ p^i p^j → Iter.q p^i ⇔ Iter.q p^j
  ;  _≡_ = λ _ _ → ⊤
  ;  id  = id⇔
  ;  _∘_ = flip _●_
  ;  assoc = tt
  ;  identityˡ = tt
  ;  identityʳ = tt
  ;  equiv = record
     { refl = tt
     ; sym = λ _ → tt
     ; trans = λ _ _ → tt
     }
  ;  ∘-resp-≡ = λ _ _ → tt
  }

iterationG : {τ : U} → (p : τ ⟷ τ) → Groupoid (iterationC p)
iterationG {τ} p = record {
    _⁻¹ = 2!
 ;  iso = λ {a} {b} {f} → record { isoˡ = tt; isoʳ = tt }
 }

-- 

1/orderC : (τ : U) → (τ ⟷ τ) → Category _ _ _
1/orderC τ pp = record {
    Obj = Iter {τ} (Prim id⟷)
 ;  _⇒_ = λ _ _ → Iter pp
 ;  _≡_ = λ p q  → Iter.q p ⇔ Iter.q q
 ;  id = zeroth pp
 ;  _∘_ = _∘i_
 ;  assoc = assoc◎r
 ;  identityˡ = idl◎l
 ;  identityʳ = idr◎l
 ;  equiv = record { refl = id⇔ ; sym = 2! ; trans = _●_ }
 ;  ∘-resp-≡ = _⊡_
 }

1/orderG : {τ : U} → (p : τ ⟷ τ) → Groupoid (1/orderC τ p)
1/orderG {τ} p = record {
    _⁻¹ = inv
 ;  iso = record { isoˡ = rinv◎l ; isoʳ = linv◎l }
 }

-- 

divC : {τ : U} → (p q : τ ⟷ τ) → Category _ _ _
divC {τ} p q = record {
    Obj = Iter p
 ; _⇒_ =  λ s t → Σ[ iq ∈ Iter q ]
            ((Iter.q s ◎ Iter.q iq) ⇔ (Iter.q iq ◎ Iter.q t))
 ; _≡_ = λ { (iter₁ , _) (iter₂ , _) → Iter.q iter₁ ⇔ Iter.q iter₂ }
 ; id = λ {A} → zeroth q , idr◎l ● idl◎r
 ; _∘_ =
   λ {  ( < j , q , αq > , pf₁)  ( < k , r , αr > , pf₂) →
   ( < j , q , αq > ∘i < k , r , αr > , 
   id⇔ ⊡ ( αq ⊡ αr ● comm-i-j j k) ● assoc◎l ● 
   (id⇔ ⊡ 2! αr ● pf₂) ⊡ id⇔ ● assoc◎r ● id⇔ ⊡ (id⇔ ⊡ 2! αq ● pf₁) ● 
   (assoc◎l ● (αr ⊡ αq ● comm-i-j k j ● 2! (αq ⊡ αr)) ⊡ id⇔)  ) }
 ; assoc = assoc◎r
 ; identityˡ = idl◎l
 ; identityʳ = idr◎l
 ; equiv = record { refl = id⇔ ; sym = 2! ; trans = _●_ }
 ; ∘-resp-≡ = _⊡_
 }

divG : {τ : U} → (p q : τ ⟷ τ) → Groupoid (divC p q)
divG {τ} p q = record {
    _⁻¹ =
    λ { {A} (q , pf) → inv q , (2! !aab⇔b ⊡ id⇔ ● assoc◎r) ●
    id⇔ {c = ! (Iter.q q)} ⊡ 2! pf ⊡ id⇔ {c = ! (Iter.q q)} ● 
    id⇔ ⊡ (assoc◎r ● ab!b⇔a)  }
 ; iso = record { isoˡ = rinv◎l; isoʳ = linv◎l }
 }

\end{code}}}}



% \newenvironment{bprooftree}
% {\leavevmode\hbox\bgroup}
% {\DisplayProof\egroup}

% \newcommand{\typ}{\texttt{ type}}
% \newcommand{\injl}[1]{\ensuremath{\texttt{inj}_l({#1})}}
% \newcommand{\injr}[1]{\ensuremath{\texttt{inj}_r({#1})}}

% Type formation, equality and introduction rules, but no elimination forms.

% \subsubsection*{Judgmental equality}

% \[
%   \begin{bprooftree}
%     \AxiomC{$A \typ$}
%     \UnaryInfC{$A = A$}
%   \end{bprooftree}
% \]

% \subsubsection*{Base types}

% \[
%   \begin{bprooftree}
%     \AxiomC{}
%     \UnaryInfC{$\mathbb{0} \typ$}
%   \end{bprooftree}
%   \quad
%   \begin{bprooftree}
%     \AxiomC{}
%     \UnaryInfC{$\mathbb{1} \typ$}
%   \end{bprooftree}
%   \quad
%   \begin{bprooftree}
%     \AxiomC{}
%     \UnaryInfC{$\bullet \in \mathbb{1}$}
%   \end{bprooftree}
% \]

% \subsubsection*{Sum and Product types}

% \[
%   \begin{bprooftree}
%     \AxiomC{$A, B \typ$}
%     \UnaryInfC{$A \oplus B \typ$}
%   \end{bprooftree}
%   \quad
%   \begin{bprooftree}
%     \AxiomC{$A = C$}
%     \AxiomC{$B = D$}
%     \BinaryInfC{$A \oplus B = C \oplus D$}
%   \end{bprooftree}
% \]

% \[
%   \begin{bprooftree}
%     \AxiomC{$A, B \typ$}
%     \AxiomC{$a \in A$}
%     \BinaryInfC{$\injl{a} \in A \oplus B$}
%   \end{bprooftree}
%   \begin{bprooftree}
%     \AxiomC{$A, B \typ$}
%     \AxiomC{$b \in B$}
%     \BinaryInfC{$\injr{b} \in A \oplus B$}
%   \end{bprooftree}
% \]

% \[
%   \begin{bprooftree}
%     \AxiomC{$A, B \typ$}
%     \UnaryInfC{$A \otimes B \typ$}
%   \end{bprooftree}
%   \quad
%   \begin{bprooftree}
%     \AxiomC{$A = C$}
%     \AxiomC{$B = D$}
%     \BinaryInfC{$A \otimes B = C \otimes D$}
%   \end{bprooftree}
% \]

% \[
%   \begin{bprooftree}
%     \AxiomC{$A, B \typ$}
%     \AxiomC{$a \in A$}
%     \AxiomC{$b \in B$}
%     \TrinaryInfC{$(a, b) \in A \otimes B$}
%   \end{bprooftree}
% \]

% \subsubsection*{Level 1 combinators}

% \[
%   \begin{bprooftree}
%     \AxiomC{$A, B \typ$}
%     \UnaryInfC{$A \leftrightarrow B \typ$}
%   \end{bprooftree}
%   \quad
%   \begin{bprooftree}
%     \AxiomC{$A = C$}
%     \AxiomC{$B = D$}
%     \BinaryInfC{$A \leftrightarrow B = C \leftrightarrow D$}
%   \end{bprooftree}
% \]

% \[
%   \begin{bprooftree}
%     \AxiomC{$A \typ$}
%     \UnaryInfC{$\texttt{unite}_{+}l \in \mathbb{0} \oplus A \leftrightarrow A$}
%   \end{bprooftree}
%   \quad
%   \begin{bprooftree}
%     \AxiomC{$A \typ$}
%     \UnaryInfC{$\texttt{unite}_{+}r \in A \leftrightarrow \mathbb{0} \oplus A$}
%   \end{bprooftree}
% \]

% \[
%   \begin{bprooftree}
%     \AxiomC{$A \typ$}
%     \UnaryInfC{$\texttt{id}\leftrightarrow \in A \leftrightarrow A$}
%   \end{bprooftree}
%   \quad
%   \begin{bprooftree}
%     \AxiomC{$A, B, C \typ$}
%     \AxiomC{$p \in A \leftrightarrow B$}
%     \AxiomC{$q \in B \leftrightarrow C$}
%     \TrinaryInfC{$p \circledcirc q \in A \leftrightarrow C$}
%   \end{bprooftree}
% \]

% \subsubsection*{Level 2 combinators}

% \[
%   \begin{bprooftree}
%     \AxiomC{$A, B \typ$}
%     \AxiomC{$p, q \in A \leftrightarrow B$}
%     \BinaryInfC{$p \Leftrightarrow q \typ$}
%   \end{bprooftree}
% \]

% \subsubsection*{Fractional types}

% \[
%   \begin{bprooftree}
%     \AxiomC{$A \typ$}
%     \AxiomC{$p \in A \leftrightarrow A$}
%     \BinaryInfC{$\#p \typ$}
%   \end{bprooftree}
% \]
% \[
%   \begin{bprooftree}
%     \AxiomC{$A \typ$}
%     \AxiomC{$p, q \in A \leftrightarrow A$}
%     \AxiomC{$r \in p \Leftrightarrow q$}
%     \TrinaryInfC{$\#p = \#q$}
%   \end{bprooftree}
% \]

% \[
%   \begin{bprooftree}
%     \AxiomC{$A \typ$}
%     \AxiomC{$p \in A \leftrightarrow A$}
%     \BinaryInfC{$1/\#p \typ$}
%   \end{bprooftree}
% \]
% \[
%   \begin{bprooftree}
%     \AxiomC{$A \typ$}
%     \AxiomC{$p, q \in A \leftrightarrow A$}
%     \AxiomC{$r \in p \Leftrightarrow q$}
%     \TrinaryInfC{$1/\#p = \mathbb{1}/\#q$}
%   \end{bprooftree}
% \]
