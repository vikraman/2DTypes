\appendix
\section{Agda Construction of Groupoids}

\AgdaHide{
\begin{code}

module appendix where

open import 2D.Types

open import Data.Sum
open import Data.Product hiding (<_,_>;,_)
open import Data.Empty
open import Data.Unit

open import Categories.Category
import Categories.Sum as C
import Categories.Product as C
open import Categories.Groupoid
import Categories.Groupoid.Sum as G
import Categories.Groupoid.Product as G
open import Level hiding (lower)

open import Relation.Binary.PropositionalEquality
open import Function
open import 2D.Power
open import 2D.Sing
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

{\setlength{\mathindent}{0cm}
\medskip
{\footnotesize{
\begin{code}

-- Construction of order groupoids #p

orderC : {τ : U} → (p : τ ⟷ τ) → Category _ _ _
orderC {τ} p = record {
      Obj = Iter p
   ;  _⇒_ = λ p^i p^j → Iter.q p^i ⇔ Iter.q p^j
   ;  _≡_ = λ _ _ → ⊤
   ;  id  = id⇔
   ;  _∘_ = λ B!C A!B → A!B ● B!C
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


orderG : {τ : U} → (p : τ ⟷ τ) → Groupoid (orderC p)
orderG {τ} p = record {
     _⁻¹ = 2!
  ;  iso = λ {a} {b} {f} → record { isoˡ = tt; isoʳ = tt }
  }

-- Construction of inverse order groupoids 1/#p

1/orderC : {τ : U} → (τ ⟷ τ) → Category _ _ _
1/orderC {τ} p = record {
     Obj = Sing p
  ;  _⇒_ = λ _ _ → Iter p 
  ;  _≡_ = λ { q r  → Iter.q q ⇔ Iter.q r }
  ;  id = zeroth p
  ;  _∘_ = λ {  < m , p , α > < n , q , β > →
                < m ℤ.+ n , p ◎ q , α ⊡ β ● 2! (lower m n) > }
  ;  assoc = assoc◎r
  ;  identityˡ = idl◎l
  ;  identityʳ = idr◎l
  ;  equiv = record { refl = id⇔ ; sym = 2! ; trans = _●_ }
  ;  ∘-resp-≡ = _⊡_
  }

1/orderG : {τ : U} → (p : τ ⟷ τ) → Groupoid (1/orderC p)
1/orderG {τ} p = record {
     _⁻¹ =  λ {  < i , q , eq > →
                 < ℤ.- i , ! q , ⇔! eq ● 2! (^⇔! {p = p} i) > }
  ;  iso =  record { isoˡ = rinv◎l ; isoʳ = linv◎l }
  }

-- construction of division groupoids #p ÷ #q

divC : {τ : U} → (p q : τ ⟷ τ) → Category _ _ _
divC {τ} p q = record {
     Obj = Iter p
  ;  _⇒_ =  λ s t → Σ[ iq ∈ Iter q ]
            ((Iter.q s ◎ Iter.q iq) ⇔ (Iter.q iq ◎ Iter.q t))
  ;  _≡_ = λ { (iter₁ , _) (iter₂ , _) → Iter.q iter₁ ⇔ Iter.q iter₂ }
  ;  id = λ {A} → zeroth q , idr◎l ● idl◎r
  ;  _∘_ = λ {  { < ia , a , αa > }
                { < ib , b , αb > }
                { < ic , c , αc > }
                ( < j , q , αq > , pf₁)
                ( < k , r , αr > , pf₂) →
                ( < j , q , αq > ∘i < k , r , αr > , 
                id⇔ ⊡ ( αq ⊡ αr ● comm-i-j j k) ● assoc◎l ● 
                (id⇔ ⊡ 2! αr ● pf₂) ⊡ id⇔ ● assoc◎r ●
                id⇔ ⊡ (id⇔ ⊡ 2! αq ● pf₁) ● 
                (assoc◎l ● (αr ⊡ αq ● comm-i-j k j ●
                2! (αq ⊡ αr)) ⊡ id⇔)  ) }
  ;  assoc = assoc◎r
  ;  identityˡ = idl◎l
  ;  identityʳ = idr◎l
  ;  equiv = record { refl = id⇔ ; sym = 2! ; trans = _●_ }
  ;  ∘-resp-≡ = _⊡_
  }

divG : {τ : U} → (p q : τ ⟷ τ) → Groupoid (divC p q)
divG {τ} p q = record {
     _⁻¹ = λ {  {A} (q , pf) → inv q ,
                (2! !aab⇔b ⊡ id⇔ ● assoc◎r) ●
                id⇔ {c = ! (Iter.q q)} ⊡ 2! pf ⊡
                id⇔ {c = ! (Iter.q q)} ● 
                id⇔ ⊡ (assoc◎r ● ab!b⇔a)  }
  ;  iso = record { isoˡ = rinv◎l; isoʳ = linv◎l }
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
