\documentclass{entcs}
\usepackage{prentcsmacro}

\def\lastname{Carette, Chen, Choudhury, and Sabry}

%% Amr
%% words to remember :-)
%% sublime unfathomable
%% path categorical semantics
%% ---

\usepackage{bbold}
\usepackage{bussproofs}
\usepackage{keystroke}
\usepackage{comment}
\usepackage{tikz}
\usepackage[inline]{enumitem}
\usepackage{stmaryrd}

\usepackage[conor]{agda}
\usepackage[mathscr]{euscript}
\usepackage[euler]{textgreek}
\usepackage{mathabx}
\usepackage{isomath}

\usepackage{microtype}
\usepackage{etoolbox}

\makeatletter
\newcommand*\NoIndentAfterEnv[1]{%
  \AfterEndEnvironment{#1}{\par\@afterindentfalse\@afterheading}}
\makeatother

\NoIndentAfterEnv{code}
\NoIndentAfterEnv{figure}

\DeclareUnicodeCharacter{120793}{$\mathbb{1}$}
\DeclareUnicodeCharacter{120794}{$\mathbb{2}$}
\DeclareUnicodeCharacter{9726}{$\sqbullet$}
\DeclareUnicodeCharacter{120792}{$\mathbb{0}$}
\DeclareUnicodeCharacter{119932}{$\mathbfit{U}$}
\DeclareUnicodeCharacter{119984}{$\mathcal{U}$}
\DeclareUnicodeCharacter{8988}{$\ulcorner$}
\DeclareUnicodeCharacter{8989}{$\urcorner$}

% \newcommand{\byiso}[1]{{\leftrightarrow}{\langle} ~#1~ \rangle}
% \newcommand{\byisotwo}[1]{{\Leftrightarrow}{\langle} ~#1~ \rangle}
\newcommand{\byiso}[1]{{\leftrightarrow₁}{\langle} ~#1~ \rangle}
\newcommand{\byisotwo}[1]{{\leftrightarrow₂}{\langle} ~#1~ \rangle}
\newcommand{\unitepl}{\texttt{unitepl}}
\newcommand{\unitipl}{\texttt{unitipl}}
\newcommand{\unitepr}{\texttt{unitepr}}
\newcommand{\unitipr}{\texttt{unitipr}}
\newcommand{\swap}{\textit{swap}}
\newcommand{\swapp}{\texttt{swapp}}
\newcommand{\assoclp}{\texttt{assoclp}}
\newcommand{\assocrp}{\texttt{assocrp}}
\newcommand{\unitetl}{\texttt{unitetl}}
\newcommand{\unititl}{\texttt{unititl}}
\newcommand{\unitetr}{\texttt{unitetr}}
\newcommand{\unititr}{\texttt{unititr}}
\newcommand{\swapt}{\texttt{swapt}}
\newcommand{\assoclt}{\texttt{assoclt}}
\newcommand{\assocrt}{\texttt{assocrt}}
\newcommand{\absorbr}{\texttt{absorbr}}
\newcommand{\absorbl}{\texttt{absorbl}}
\newcommand{\factorzr}{\texttt{factorzr}}
\newcommand{\factorzl}{\texttt{factorzl}}
\newcommand{\factor}{\texttt{factor}}
\newcommand{\distl}{\texttt{distl}}
\newcommand{\dist}{\texttt{dist}}
\newcommand{\factorl}{\texttt{factorl}}
\newcommand{\id}{\textit{id}}
\newcommand{\compc}[2]{#1 \circ #2}
\newcommand{\compcc}[2]{#1 \bullet #2}
\newcommand{\respcomp}[2]{#1 \odot #2}
\newcommand{\trunc}{\textit{trunc}}

\newcommand{\Typ}{\mathbf{Type}}
\newcommand{\alt}{~\mid~}
\newcommand{\patht}[1]{\textsc{PATHS}(#1,#1)}
\newcommand{\fpatht}[1]{\textsc{FREEPATHS}(#1,\Box)}
\newcommand{\fpathp}[2]{\textsc{freepath}~#1~#2}
\newcommand{\pathind}[2]{\textsc{pathind}~#1~#2}
\newcommand{\invc}[1]{!\;#1}
\newcommand{\evalone}[2]{eval(#1,#2)}
\newcommand{\evalbone}[2]{evalB(#1,#2)}
\newcommand{\reflp}{\textsc{refl}}
\newcommand{\notp}{\textsc{not}}
\newcommand{\gluep}{\textsc{glue}}
\newcommand{\reflh}{\mathit{refl}_{\sim}}
\newcommand{\symh}[1]{\mathit{sym}_{\sim}~#1}
\newcommand{\transh}[2]{\mathit{trans}_{\sim}~#1~#2}
\newcommand{\reflq}{\mathit{refl}_{\simeq}}
\newcommand{\symq}[1]{\mathit{sym}_{\simeq}~#1}
\newcommand{\transq}[2]{\mathit{trans}_{\simeq}~#1~#2}
\newcommand{\isequiv}[1]{\mathit{isequiv}(#1)}
\newcommand{\idc}{\mathit{id}_{\boolt}}
\newcommand{\swapc}{\mathit{swap}_{\boolt}}
\newcommand{\assocc}{\mathit{assoc}}
\newcommand{\invl}{\mathit{invl}}
\newcommand{\invr}{\mathit{invr}}
\newcommand{\invinv}{\mathit{inv}^2}
\newcommand{\idlc}{\mathit{idl}}
\newcommand{\idrc}{\mathit{idr}}
\newcommand{\swapswap}{\swapc^2}
\newcommand{\compsim}{\compc_{\isotwo}}
% \newcommand{\iso}{\leftrightarrow}
% \newcommand{\isotwo}{\Leftrightarrow}
\newcommand{\iso}{\leftrightarrow₁}
\newcommand{\isotwo}{\leftrightarrow₂}
\newcommand{\isothree}{\leftrightarrow₃}
\newcommand{\piso}{\multimapdotbothB~~}
\newcommand{\zt}{\mathbb{0}}
\newcommand{\ot}{\mathbb{1}}
\newcommand{\bt}{\mathbb{2}}
\newcommand{\fc}{\mathit{false}}
\newcommand{\tc}{\mathit{true}}
\newcommand{\boolt}{\mathbb{B}}
\newcommand{\univ}{\mathcal{U}}
\newcommand{\uzero}{\mathcal{U}_0}
\newcommand{\uone}{\mathcal{U}_1}
\newcommand{\Rule}[2]{
\makebox{
$\displaystyle
\frac{\begin{array}{l}#1\\\end{array}}
{\begin{array}{l}#2\\\end{array}}$}}
\newcommand{\proves}{\vdash}
\newcommand{\jdgg}[3]{#1 \proves #2 : #3}
\newcommand{\jdg}[2]{\proves #1 : #2}
\newcommand{\jdge}[3]{\proves #1 = #2 : #3}
%% codes
%% denotations

% TODO: give this a better name!
\newcommand{\bracket}[1]{\ensuremath{\{#1\}}}
\newcommand{\ptrunc}[1]{\ensuremath{\| #1 \|}}
\newcommand{\dbracket}[1]{\ensuremath{\llbracket \; #1 \; \rrbracket}}
\let\oldPi\Pi
\renewcommand{\Pi}{\mathrm\oldPi}
\newcommand{\PiTwo}{\ensuremath{\mathrm\Pi_{\mathbb{2}}}}
\newcommand{\amr}[1]{\fbox{\begin{minipage}{0.8\textwidth}\color{red}{Amr says: {#1}}\end{minipage}}}
\newcommand{\jacques}[1]{\fbox{\begin{minipage}{0.8\textwidth}\color{red}{Jacques says: {#1}}\end{minipage}}}

\newcommand{\newnote}[2]{{\sf {#1} $\clubsuit$ {#2} $\clubsuit$}}
\newcommand{\VC}[1]{{\color{orange}{\newnote{VC}{#1}}}}

\newcommand{\newtext}[1]{{\color{purple}{#1}}}

\begin{document}

\begin{frontmatter}
  \title{From Reversible Programs to \\ Univalent Universes and Back}
  \author{Jacques Carette}
  \address{McMaster University}
  \author{Chao-Hong Chen}
  \author{Vikraman Choudhury}
  \author{Amr Sabry}
  \address{Indiana University}

  \begin{abstract}
    We establish a close connection between a reversible programming
    language based on type isomorphisms and a formally presented
    univalent universe. The correspondence relates combinators
    witnessing type isomorphisms in the programming language to paths in
    the univalent universe; and combinator optimizations in the
    programming language to 2-paths in the univalent universe. The
    result suggests a simple computational interpretation of paths and
    of univalence in terms of familiar programming constructs whenever
    the universe in question is computable.
  \end{abstract}
\end{frontmatter}

\AgdaHide{
\begin{code}
{-# OPTIONS --without-K --type-in-type --allow-unsolved-metas #-}
module upi where

𝒰 = Set

data ⊥ : 𝒰 where

record ⊤ : 𝒰 where
  constructor tt

record Σ (A : 𝒰) (B : A → 𝒰) : 𝒰 where
  constructor _,_
  field
    pr₁ : A
    pr₂ : B pr₁

open Σ public
infixr 4 _,_
syntax Σ A (λ a → B) = Σ[ a ∶ A ] B

infix 2 _×_
_×_ : (A B : 𝒰) → 𝒰
A × B = Σ A (λ _ → B)

data _+_ (A B : 𝒰) : 𝒰 where
  inl : (x : A) → A + B
  inr : (y : B) → A + B

Π : (A : 𝒰) (B : A → 𝒰) → 𝒰
Π A B = (a : A) → B a

syntax Π A (λ a → B) = Π[ a ∶ A ] B

id : {A : 𝒰} → A → A
id a = a

infix 4 _∘_
_∘_ : {A : 𝒰} {B : A → 𝒰} {C : {a : A} → B a → 𝒰}
    → (g : {a : A} → (b : B a) → C b) (f : (a : A) → B a)
    → (a : A) → C (f a)
g ∘ f = λ a → g (f a)

infix 3 _==_
data _==_ {A : 𝒰} : A → A → 𝒰 where
  refl : (a : A) → a == a

infix 100 !_
!_ : {A : 𝒰} {a b : A} → (a == b) → (b == a)
!_ (refl _) = refl _

infixr 80 _◾_
_◾_ : {A : 𝒰} {a b c : A} → (a == b) → (b == c) → (a == c)
_◾_ (refl _) (refl _) = refl _

infix 3 _∼_
_∼_ : {A : 𝒰} {B : A → 𝒰} (f g : (a : A) → B a) → 𝒰
_∼_ {A} f g = (a : A) → f a == g a

coe : {A B : 𝒰} (p : A == B) → A → B
coe (refl A) = id

ap : {A B : 𝒰} {x y : A} → (f : A → B) (p : x == y) → f x == f y
ap f (refl x) = refl (f x)

transport : {A : 𝒰} (P : A → 𝒰) {x y : A} → x == y → P x → P y
transport P = coe ∘ ap P

PathOver : {A : 𝒰} (P : A → 𝒰) {x y : A} (p : x == y) (u : P x) (v : P y) → 𝒰
PathOver P p u v = transport P p u == v

syntax PathOver P p u v = u == v [ P ↓ p ]

apd : {A : 𝒰} {P : A → 𝒰} {x y : A} (f : (a : A) → P a) (p : x == y) → f x == f y [ P ↓ p ]
apd f (refl x) = refl (f x)

⊥-elim : {C : 𝒰} → ⊥ → C
⊥-elim ()

module _ {X : 𝒰} where

  ◾unitr : {x y : X} → (p : x == y) → p ◾ refl y == p
  ◾unitr (refl x) = refl (refl x)

  ◾unitl : {x y : X} → (p : x == y) → refl x ◾ p == p
  ◾unitl (refl x) = refl (refl x)

  ◾invr : {x y : X} → (p : x == y) → ! p ◾ p == refl y
  ◾invr (refl x) = refl (refl x)

  ◾invl : {x y : X} → (p : x == y) → p ◾ ! p == refl x
  ◾invl (refl x) = refl (refl x)

  !! : {x y : X} → (p : x == y) → ! (! p) == p
  !! (refl x) = refl (refl x)

  !◾ : {x y z : X} → (p : x == y) → (q : y == z) → ! (p ◾ q) == ! q ◾ ! p
  !◾ (refl y) (refl .y) = refl (refl y)

  infixr 80 _[1,0,2]_
  _[1,0,2]_ : {x y z : X} → {r s : y == z}
              → (p : x == y) → r == s → p ◾ r == p ◾ s
  (refl y) [1,0,2] γ = ◾unitl _ ◾ γ ◾ ! (◾unitl _)

  ◾assoc : {w x y z : X} → (p : w == x) → (q : x == y) → (r : y == z)
           → (p ◾ q) ◾ r == p ◾ q ◾ r
  ◾assoc p q (refl y) = ◾unitr _ ◾ (p [1,0,2] ! (◾unitr _))

  infixr 80 _[2,0,1]_
  _[2,0,1]_ : {x y z : X} → {p q : x == y}
              → p == q → (r : y == z) → p ◾ r == q ◾ r
  α [2,0,1] (refl y) = ◾unitr _ ◾ α ◾ ! (◾unitr _)

  infixr 80 _[2,0,2]_
  _[2,0,2]_ : {x y z : X} → {p q : x == y} → {r s : y == z}
              → p == q → r == s → p ◾ r == q ◾ s
  _[2,0,2]_ {q = q} {r} α β = (α [2,0,1] r) ◾ (q [1,0,2] β)

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction}

The proceedings of the $2012$ Symposium on Principles of Programming
Languages~\cite{Field:2012:2103656} included two apparently unrelated papers:
\emph{Information Effects} by James and Sabry and \emph{Canonicity for
  2-dimensional type theory} by Licata and Harper. The first paper, motivated by
the physical nature of
computation~\cite{Landauer:1961,PhysRevA.32.3266,Toffoli:1980,bennett1985fundamental,Frank:1999:REC:930275},
proposed, among other results, a reversible language $\Pi$ in which every
program is a type isomorphism. The second paper, motivated by the connections
between homotopy theory and type theory~\cite{vv06,hottbook}, proposed a
judgmental formulation of intensional dependent type theory with a
twice-iterated identity type. During the presentations and ensuing discussions
at the conference, it became apparent, at an intuitive and informal level, that
the two papers had strong similarities. Formalizing the precise connection was
far from obvious, however.

Here we report on a formal connection between appropriately formulated
reversible languages on one hand and univalent universes on the
other. In the next section, we give a rational reconstruction of the
reversible programming language $\Pi$, focusing on a small
``featherweight'' fragment~$\PiTwo$. In Sec.~\ref{sec:univalent}, we
review basic homotopy type theory (HoTT) background leading to
\emph{univalent fibrations} which allow us to give formal
presentations of ``small'' univalent universes. In
Sec.~\ref{sec:model} we define and establish the basic properties of
such a univalent subuniverse {\small\AgdaFunction{Ũ[𝟚]}} which we
prove in Sec.~\ref{sec:correspondence} as sound and complete with
respect to the reversible language $\PiTwo$.
Sec.~\ref{sec:discussion} discusses the implications of our work and
situates it into the broader context of the existing literature.
%% Sec.~\ref{sec:conclusion} right now is a stub, and may not
%% survive?

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Reversible Programming Languages}

Starting from the physical principle of ``conservation of
information''~\cite{Hey:1999:FCE:304763,fredkin1982conservative}, James and
Sabry~\cite{James:2012:IE:2103656.2103667} proposed a family of programming
languages $\Pi$ in which computation preserves information. Technically,
computations are \emph{type isomorphisms} which, at least in the case of finite
types, clearly preserve entropy in the information-theoretic
sense~\cite{James:2012:IE:2103656.2103667}. We illustrate the general flavor of
the family of languages with some examples and then identify a ``featherweight''
version of $\Pi$, called $\PiTwo$, to use in our formal development.

%%%%%
\subsection{Examples}

The examples below assume a representation of the type of booleans
${\small\bt}$ as the disjoint union ${\small\ot \oplus \ot}$ with the
left injection representing ${\small\mathsf{false}}$ and the right
injection representing ${\small\mathsf{true}}$. Given an arbitrary
reversible function {\small\AgdaFunction{f}} of type
${\small a \iso a}$, we can build the reversible function
${\small\AgdaFunction{controlled}~\AgdaFunction{f}}$ that takes a pair
of type ${\small\bt \otimes a}$ and checks the incoming boolean; if it
is false (i.e., we are in the left injection), the function behaves
like the identity; otherwise the function applies {\small\AgdaFunction{f}}
to the second argument. The incoming boolean is then reconstituted to
maintain reversibility:

{\small
\[\def\arraystretch{1.2}\begin{array}{rcll}
\AgdaFunction{controlled}  &:& \forall a.~ (a \iso a) \quad\rightarrow
                            & ~(\bt \otimes a \iso \bt \otimes a) \\
\AgdaFunction{controlled}~\AgdaFunction{f} &=&

  \bt \otimes a
    & \byiso{\AgdaFunction{unfoldBool} \otimes \AgdaFunction{id}} \\
&& (\ot \oplus \ot) \otimes a
    & \byiso{\AgdaFunction{distribute}} \\
&& (\ot \otimes a) \oplus (\ot \otimes a)
    & \byiso{\AgdaFunction{id} \oplus (\AgdaFunction{id} \otimes \AgdaFunction{f})} \\
&& (\ot \otimes a) \oplus (\ot \otimes a)
    & \byiso{\AgdaFunction{factor}} \\
&& (\ot \oplus \ot) \otimes a
    & \byiso{\AgdaFunction{foldBool} \otimes \AgdaFunction{id}} \\
&& \bt \otimes a & ~ \\
\end{array}
\]}

\noindent The left column shows the sequence of types that are visited
during the computation; the right column shows the names of the
combinators\footnote{We use names that are hopefully quite mnemonic;
  for the precise definitions of the combinators see the
  $\Pi$-papers~\cite{James:2012:IE:2103656.2103667,rc2011,rc2012,theseus,Carette2016}
  or the accompanying code at
  \url{https://git.io/v7wtW}.} that witness the
corresponding type isomorphism. The code for
{\small\AgdaFunction{controlled}~\AgdaFunction{f}} provides
constructive evidence (i.e., a program, a logic gate, or a hardware
circuit) for an automorphism on ${\small\bt \otimes a}$: it can be read
top-down or bottom-up to go back and forth.

The {\small\AgdaFunction{not}} function below is a simple lifting of
{\small\AgdaFunction{swap₊}} which swaps the left and right injections of a sum
type. Using the {\small\AgdaFunction{controlled}} building block, we can build a
controlled-not ({\small\AgdaFunction{cnot}}) gate and a controlled-controlled-not
gate, also known as the {\small\AgdaFunction{toffoli}} gate. The latter gate is a
universal function for combinational boolean circuits thus showing the
expressiveness of the language:

{\small
\[\begin{array}{rcl}
\AgdaFunction{not} &:& \bt \iso \bt \\
\AgdaFunction{not} &=&
  \AgdaFunction{unfoldBool} \odot_1 \AgdaFunction{swap₊} \odot_1 \AgdaFunction{foldBool} \\
\\
\AgdaFunction{cnot} &:& \bt \otimes \bt \iso \bt \otimes \bt \\
\AgdaFunction{cnot} &=& \AgdaFunction{controlled}~\AgdaFunction{not} \\
\\
\AgdaFunction{toffoli} &:& \bt \otimes (\bt \otimes \bt)
                           \iso \bt \otimes (\bt \otimes \bt) \\
\AgdaFunction{toffoli} &=& \AgdaFunction{controlled}~\AgdaFunction{cnot} \\
\end{array}\]}
%%%

\noindent While we wrote {\small\AgdaFunction{controlled}} in
equational-reasoning style, {\small\AgdaFunction{not}} is written in
the point-free combinator style.  These are equivalent as ${\small\byiso{-}}$
is defined in terms of the sequential composition combinator
${\small\odot_1}$.

As is customary in any semantic perspective on programming languages, we are
interested in the question of when two programs are ``equivalent.'' Consider the
following six programs of type~${\small\bt \iso \bt}$:

{\small
\[\def\arraystretch{1.2}\begin{array}{rcl}
\AgdaFunction{id₁}~\AgdaFunction{id₂}~\AgdaFunction{id₃}~
  \AgdaFunction{not₁}~\AgdaFunction{not₂}~\AgdaFunction{not₃} &:& \bt \iso \bt \\
\AgdaFunction{id₁} &=&
  \AgdaFunction{id} \odot_1 \AgdaFunction{id} \\
\AgdaFunction{id₂} &=&
  \AgdaFunction{not} \odot_1 \AgdaFunction{id} \odot_1 \AgdaFunction{not} \\
\AgdaFunction{id₃} &=&
  \AgdaFunction{uniti⋆} \odot_1 \AgdaFunction{swap⋆} \odot_1
                        (\AgdaFunction{id} \otimes \AgdaFunction{id}) \odot_1
                        \AgdaFunction{swap⋆} \odot_1
                        \AgdaFunction{unite⋆} \\
\AgdaFunction{not₁} &=&
  \AgdaFunction{id} \odot_1 \AgdaFunction{not} \\
\AgdaFunction{not₂} &=&
  \AgdaFunction{not} \odot_1 \AgdaFunction{not} \odot_1 \AgdaFunction{not} \\
\AgdaFunction{not₃} &=&
  \AgdaFunction{uniti⋆} \odot_1 \AgdaFunction{swap⋆} \odot_1
                        (\AgdaFunction{not} \otimes \AgdaFunction{id}) \odot_1
                        \AgdaFunction{swap⋆} \odot_1
                        \AgdaFunction{unite⋆}
\end{array}\]}

\begin{figure}
\begin{center}
\begin{tikzpicture}[scale=0.9,every node/.style={scale=0.9}]
  \draw (1,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (1,2) circle [radius=0.025];
  \node[below] at (1,2) {*};

  \draw (0,0) ellipse (0.5cm and 1cm);
  \draw[fill] (0,0.5) circle [radius=0.025];
  \node[below] at (0,0.5) {F};
  \draw[fill] (0,-0.5) circle [radius=0.025];
  \node[below] at (0,-0.5) {T};

  \draw     (1,2)    -- (2,2)      ; %% ()
  \draw     (0,0.5)  -- (2,0.5)    ; %% F
  \draw     (0,-0.5) -- (2,-0.5)   ; %% T

  \draw     (2,2)    -- (3,-0.5)   ;
  \draw     (2,0.5)  -- (3,2)      ;
  \draw     (2,-0.5) -- (3,1)      ;

  \draw     (3,2)    -- (3.5,2)    ;
  \draw     (3,1)    -- (3.5,1)    ;
  \draw     (3,-0.5) -- (3.5,-0.5) ;

  \draw     (3.5,2)    -- (4.5,1)    ;
  \draw     (3.5,1)    -- (4.5,2)    ;
  \draw     (3.5,-0.5) -- (4.5,-0.5) ;

  \draw     (4.5,2)    -- (5,2)    ;
  \draw     (4.5,1)    -- (5,1)    ;
  \draw     (4.5,-0.5) -- (5,-0.5) ;

  \draw     (5,2)    -- (6,0.5)  ;
  \draw     (5,1)    -- (6,-0.5) ;
  \draw     (5,-0.5) -- (6,2)    ;

  \draw     (6,2)    -- (7,2)    ;
  \draw     (6,0.5)  -- (8,0.5)  ;
  \draw     (6,-0.5) -- (8,-0.5) ;

  \draw (7,2) ellipse (0.5cm and 0.5cm);
  \draw[fill] (7,2) circle [radius=0.025];
  \node[below] at (7,2) {*};

  \draw (8,0) ellipse (0.5cm and 1cm);
  \draw[fill] (8,0.5) circle [radius=0.025];
  \node[below] at (8,0.5) {F};
  \draw[fill] (8,-0.5) circle [radius=0.025];
  \node[below] at (8,-0.5) {T};

\end{tikzpicture}
\end{center}
\caption{\label{fig:not}Graphical representation of {\small\AgdaFunction{not₃}}}
\end{figure}

The programs are all of the same type but this is clearly not a
sufficient condition for ``equivalence.'' Thinking extensionally,
i.e., by looking at all possible input-output pairs, it is easy to
verify that the six programs split into two classes: one consisting of
the first three programs which are all equivalent to the identity
function and the other consisting of the remaining three programs
which all equivalent to boolean negation. In the context of $\Pi$, we
can provide \emph{evidence} (i.e., a reversible program of type
$\isotwo$ that manipulates lower level reversible programs of type
$\iso$ ) that can constructively identify programs in each equivalence
class. We show such a level-2 program proving that
{\small\AgdaFunction{not₃}} is equivalent to
{\small\AgdaFunction{not}}. For illustration, the program for
{\small\AgdaFunction{not₃}} is depicted in Fig.~\ref{fig:not}. We
encourage the reader to map the steps below to manipulations on the
diagram that would incrementally simplify it:

{\small
\[\def\arraystretch{1.2}\begin{array}{rcll}
\AgdaFunction{notOpt} &:& \AgdaFunction{not₃} \isotwo \AgdaFunction{not} \\
\AgdaFunction{notOpt} &=&
  \AgdaFunction{uniti⋆} \odot_1 (\AgdaFunction{swap⋆} \odot_1
                        ((\AgdaFunction{not} \otimes \AgdaFunction{id}) \odot_1
                        (\AgdaFunction{swap⋆} \odot_1 \AgdaFunction{unite⋆})))
 & \quad\byisotwo{\AgdaFunction{id} \boxdot \AgdaFunction{assocLeft}} \\
&& \AgdaFunction{uniti⋆} \odot_1 (\AgdaFunction{swap⋆} \odot_1
                        (\AgdaFunction{not} \otimes \AgdaFunction{id})) \odot_1
                        (\AgdaFunction{swap⋆} \odot_1 \AgdaFunction{unite⋆})
 & \quad\byisotwo{\AgdaFunction{id} \boxdot (\AgdaFunction{swapLeft}
                                  \boxdot \AgdaFunction{id})} \\
&& \AgdaFunction{uniti⋆} \odot_1 ((\AgdaFunction{id} \otimes \AgdaFunction{not})
                      \odot_1 \AgdaFunction{swap⋆}) \odot_1
                        (\AgdaFunction{swap⋆} \odot_1 \AgdaFunction{unite⋆})
 & \quad\byisotwo{\AgdaFunction{id} \boxdot \AgdaFunction{assocRight}} \\
&& \AgdaFunction{uniti⋆} \odot_1 ((\AgdaFunction{id} \otimes \AgdaFunction{not})
                      \odot_1 (\AgdaFunction{swap⋆} \odot_1
                        (\AgdaFunction{swap⋆} \odot_1 \AgdaFunction{unite⋆})))
 & \quad\byisotwo{\AgdaFunction{id} \boxdot (\AgdaFunction{id}
                                  \boxdot \AgdaFunction{assocLeft})} \\
&& \AgdaFunction{uniti⋆} \odot_1 ((\AgdaFunction{id} \otimes \AgdaFunction{not})
                      \odot_1 ((\AgdaFunction{swap⋆} \odot_1
                      \AgdaFunction{swap⋆}) \odot_1 \AgdaFunction{unite⋆}))
 & \quad\byisotwo{\AgdaFunction{id} \boxdot (\AgdaFunction{id}
                                  \boxdot (\AgdaFunction{leftInv} \boxdot \AgdaFunction{id}))} \\
&& \AgdaFunction{uniti⋆} \odot_1 ((\AgdaFunction{id} \otimes \AgdaFunction{not})
                      \odot_1 (\AgdaFunction{id} \odot_1 \AgdaFunction{unite⋆}))
 & \quad\byisotwo{\AgdaFunction{id} \boxdot (\AgdaFunction{id}
                                  \boxdot \AgdaFunction{idLeft})} \\
&& \AgdaFunction{uniti⋆} \odot_1 ((\AgdaFunction{id} \otimes \AgdaFunction{not})
                      \odot_1 \AgdaFunction{unite⋆})
 & \quad\byisotwo{\AgdaFunction{assocLeft}} \\
&& (\AgdaFunction{uniti⋆} \odot_1 (\AgdaFunction{id} \otimes \AgdaFunction{not}))
                      \odot_1 \AgdaFunction{unite⋆}
 & \quad\byisotwo{\AgdaFunction{unitiLeft} \boxdot \AgdaFunction{id}} \\
&& (\AgdaFunction{not} \odot_1 \AgdaFunction{uniti⋆}) \odot_1 \AgdaFunction{unite⋆}
 & \quad\byisotwo{\AgdaFunction{assocRight}} \\
&& \AgdaFunction{not} \odot_1 (\AgdaFunction{uniti⋆} \odot_1 \AgdaFunction{unite⋆})
 & \quad\byisotwo{\AgdaFunction{id} \boxdot \AgdaFunction{leftInv}} \\
&& \AgdaFunction{not} \odot_1 \AgdaFunction{id}
 & \quad\byisotwo{\AgdaFunction{idRight}} \\
&& \AgdaFunction{not}
\end{array}\]}

\noindent It is worthwhile mentioning that the above derivation could also be
drawn as one (large!) commutative diagram in an appropriate category, with each
$\byisotwo{-}$ as a $2$-arrow (and representing a natural isomorphism).  See
Shulman's draft book~\cite{shulman} for that interpretation.

%%%%%
\subsection{A Small Reversible Language of Booleans: \PiTwo}{\label{sec:pi2}}

Having illustrated the general flavor of the $\Pi$ family of
languages, we present in full detail an Agda-based formalization of a
small $\Pi$-based language which we will use to establish the
connection to an explicit univalent universe. The language is the
restriction of $\Pi$ to the case of just one type $\mathbb{2}$:

%% \[\def\arraystretch{0.8}\begin{array}{l@{\quad}rclrl}
%% (\textit{Types}) & \tau &::=& \bt \\
%% \\
%% (\textit{Terms}) &  v &::=& \fc &:& \bt \\
%%               && \alt & \tc &:& \bt \\
%% \\
%%  (\textit{1-combinators}) &  c &::=& \id &:& \tau \iso \tau \\
%%                && \alt & \swap &:& \bt \iso \bt \\
%%                && \alt & ! &:& (\tau_1 \iso \tau_2) \to (\tau_2 \iso \tau_1) \\
%%                && \alt & \odot_1 &:& (\tau_1 \iso \tau_2) \to (\tau_2 \iso \tau_3) \to (\tau_1 \iso \tau_3)  \\
%% \\
%% (\textit{2-combinators}) & \alpha &::=& \id &:& c \isotwo c \\
%%             && \alt & \idlc &:& \compc{\id}{c} \isotwo c \\
%%             && \alt & \idrc &:& \compc{c}{\id} \isotwo c \\
%%             && \alt & \invl &:& \compc{c\;}{\;\invc{c}} \isotwo \id \\
%%             && \alt & \invr &:& \compc{\invc{c}}{c} \isotwo \id \\
%%             && \alt & \rho &:& \swap \circ \swap \isotwo \id \\
%%             && \alt & \assocc &:&
%%                                   \compc{(\compc{c_1}{c_2})}{c_3} \isotwo \compc{c_1}{(\compc{c_2}{c_3})} \\
%%             && \alt & \boxdot &:& (c_1 \isotwo c_1') \to (c_2 \isotwo c_2') \to
%%                              (\compc{c_1}{c_2} \isotwo \compc{c_1'}{c_2'}) \\
%%             && \alt & !! &:& (c_1 \isotwo c_2) \to (c_2 \isotwo c_1) \\
%%             && \alt & \bullet &:& (c_1 \isotwo c_2) \to (c_2 \isotwo c_3) \to (c_1 \isotwo c_3)
%% \end{array}\]

\begin{code}
data 𝟚 : 𝒰 where
  0₂ 1₂ : 𝟚
\end{code}

The syntax of \PiTwo\ is given by the following four Agda
definitions. The first definition~{\small\AgdaFunction{Π₂}} introduces
the set of types of the language: this set contains
just~{\small\AgdaInductiveConstructor{`𝟚}} which is a name for the
type of booleans $\mathbb{2}$. The next three definitions introduce
the programs (combinators) in the language stratified by levels. The
level-1 programs of type $\iso$ map between types; the level-2
programs of type $\isotwo$ map between level-1 programs; and the
level-3 programs of type $\isothree$ map between level-2 programs:

\AgdaHide{
\begin{code}
infix 3 _⟷₁_ _⟷₂_ _⟷₃_
infix 5 !₁_ !₂_
infix 4 _⊙₁_ _⊙₂_
\end{code}
}

\begin{code}
data Π₂ : 𝒰 where
  `𝟚 : Π₂

---------------
data _⟷₁_ : (A B : Π₂) → 𝒰 where

  `id    : ∀ {A} → A ⟷₁ A
  `not   : `𝟚 ⟷₁ `𝟚

  !₁_    : ∀ {A B} → (A ⟷₁ B) → (B ⟷₁ A)
  _⊙₁_   : ∀ {A B C} → (A ⟷₁ B) → (B ⟷₁ C) → (A ⟷₁ C)

---------------
data _⟷₂_ : ∀ {A B} (p q : A ⟷₁ B) → 𝒰 where

  `id₂   : ∀ {A B} {p : A ⟷₁ B} → p ⟷₂ p

  !₂_    : ∀ {A B} {p q : A ⟷₁ B} → (p ⟷₂ q) → (q ⟷₂ p)
  _⊙₂_   : ∀ {A B} {p q r : A ⟷₁ B} → (p ⟷₂ q) → (q ⟷₂ r) → (p ⟷₂ r)

  `idl   : ∀ {A B} (p : A ⟷₁ B) → `id ⊙₁ p ⟷₂ p
  `idr   : ∀ {A B} (p : A ⟷₁ B) → p ⊙₁ `id ⟷₂ p
  `assoc : ∀ {A B C D} (p : A ⟷₁ B) (q : B ⟷₁ C) (r : C ⟷₁ D)
         → (p ⊙₁ q) ⊙₁ r ⟷₂ p ⊙₁ (q ⊙₁ r)

  _□₂_   : ∀ {A B C} {p q : A ⟷₁ B} {r s : B ⟷₁ C}
         → (p ⟷₂ q) → (r ⟷₂ s) → (p ⊙₁ r) ⟷₂ (q ⊙₁ s)
  `!     : ∀ {A B} {p q : A ⟷₁ B} → (p ⟷₂ q) → (!₁ p ⟷₂ !₁ q)
  `!l    : ∀ {A B} (p : A ⟷₁ B) → (p ⊙₁ !₁ p ⟷₂ `id)
  `!r    : ∀ {A B} (p : B ⟷₁ A) → (!₁ p ⊙₁ p ⟷₂ `id)

  `!id   : ∀ {A} → !₁ `id {A} ⟷₂ `id {A}
  `!not  : !₁ `not ⟷₂ `not

  `!◾    : ∀ {A B C} {p : A ⟷₁ B} {q : B ⟷₁ C}
         → !₁ (p ⊙₁ q) ⟷₂ (!₁ q) ⊙₁ (!₁ p)
  `!!    : ∀ {A B} {p : A ⟷₁ B} → !₁ (!₁ p) ⟷₂ p

---------------
data _⟷₃_ {A B} {p q : A ⟷₁ B} (u v : p ⟷₂ q) : 𝒰 where
  `trunc : u ⟷₃ v
\end{code}

% \jacques{The text below doesn't make sense anymore as the
% ``syntactic categories'' were named in the above
% commented out array, but have different names in the Agda
% code.}

In the previous presentations of
$\Pi$~\cite{rc2011,James:2012:IE:2103656.2103667,Carette2016}, the level-3
programs, consisting of just one trivial program
{\small\AgdaInductiveConstructor{`trunc}}, were not made explicit. The much
larger level-1 and level-2 programs of the full $\Pi$
language~\cite{Carette2016} have been specialized to our small language. For the
level-1 constructors, denoting reversible programs, type isomorphisms,
permutations between finite sets, or equivalences depending on one's favorite
interpretation, we have two canonical programs
{\small\AgdaInductiveConstructor{`id}} and
{\small\AgdaInductiveConstructor{`not}} closed under inverses
{\small\AgdaInductiveConstructor{!₁}} and sequential
composition~{\small\AgdaInductiveConstructor{⊙₁}}. For level-2 constructors,
denoting reversible program transformations, coherence conditions on type
isomorphisms, equivalences between permutations, or program optimizations
depending on one's favorite interpretation, we have the following groups: (i)
the first group contains the identity, inverses, and sequential composition;
(ii) the second group establishes the coherence laws for level-1 sequential
composition (e.g, it is associative); and (iii) finally the third group includes
general rules for inversions of level-1 constructors.

Each of the level-2 combinators of type $p \isotwo q$ is easily seen
to establish an equivalence between level-1 programs $p$ and $q$ (as
shown in previous work~\cite{Carette2016} and in
Sec.~\ref{sec:correspondence}). For example, composition of negation
is equivalent to the identity:

\begin{code}
not⊙₁not⟷₂id : `not ⊙₁ `not ⟷₂ `id
not⊙₁not⟷₂id = ((!₂ `!not) □₂ `id₂) ⊙₂ (`!r `not)
\end{code}

What is particularly interesting, however, is that the collection of
level-2 combinators above is \emph{complete} in the sense that any
equivalence between level-1 programs $p$ and $q$ can be proved using
the level-2 combinators. Formally we have two canonical level-1
programs {\small\AgdaInductiveConstructor{`id}} and
{\small\AgdaInductiveConstructor{`not}} and for any level-1 program
${\small p}$, we have evidence that either
${\small p \isotwo \AgdaInductiveConstructor{`id}}$ or
${\small p \isotwo \AgdaInductiveConstructor{`not}}$.

To prove this, we introduce a type which encodes the knowledge of
which level-1 programs are canonical. The type {\small\AgdaDatatype{Which}}
names the subset of {\small\AgdaDatatype{⟷₁}} which are canonical forms:

\begin{code}
data Which : 𝒰 where
  ID NOT : Which

refine : (w : Which) → `𝟚 ⟷₁ `𝟚
refine ID = `id
refine NOT = `not
\end{code}

This enables us to compute for any 2-combinator $c$ (the name of) its canonical
form, as well as a proof that $c$ is equivalent to its canonical form:

\begin{code}
canonical : (c : `𝟚 ⟷₁ `𝟚) → Σ[ c' ∶ Which ] (c ⟷₂ refine c')
canonical `id = ID , `id₂
canonical `not = NOT , `id₂
canonical (!₁ c) with canonical c
... | ID , c⟷₂id = ID , (`! c⟷₂id ⊙₂ `!id)
... | NOT , c⟷₂not = NOT , (`! c⟷₂not ⊙₂ `!not)
canonical (_⊙₁_ {_} {`𝟚} c₁ c₂) with canonical c₁ | canonical c₂
... | ID , c₁⟷₂id | ID , c₂⟷₂id = ID , ((c₁⟷₂id □₂ c₂⟷₂id) ⊙₂ `idl `id)
... | ID , c₁⟷₂id | NOT , c₂⟷₂not = NOT , ((c₁⟷₂id □₂ c₂⟷₂not) ⊙₂ `idl `not)
... | NOT , c₁⟷₂not | ID , c₂⟷₂id = NOT , ((c₁⟷₂not □₂ c₂⟷₂id) ⊙₂ `idr `not)
... | NOT , c₁⟷₂not | NOT , c₂⟷₂not = ID , ((c₁⟷₂not □₂ c₂⟷₂not) ⊙₂ not⊙₁not⟷₂id)
\end{code}

It is worthwhile to note that the proof of
{\small\AgdaFunction{canonical}} does not use all the level-2
combinators. The larger set of 2-combinators is however useful to
establish a more direct connection with the model presented in the
next sections.

% \begin{lemma}[Canonical Forms]
%   Given a 1-combinator $c : \tau \iso \tau$, we either have a
%   2-combinator of type $c \isotwo \AgdaFunction{`id}$ or a 2-combinator of type
%   $c \isotwo \AgdaFunction{`not}$. In other words, every 1-combinator has a canonical
%   representation as either $\AgdaFunction{`id}$ or $\AgdaFunction{`not}$ and the set of 2-combinators is rich
%   enough to normalize $c$ to its canonical representation.
% \end{lemma}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{HoTT Background}
\label{sec:univalent}

We work in intensional type theory with one univalent universe
{\small\AgdaPrimitiveType{𝒰}} closed under propositional truncation.  The rest
of this section is devoted to explaining what that means.  We follow
the terminology used in the HoTT book~\cite{hottbook}.  For brevity,
we will often just give type signatures and elide the term. The details
can be found in the accompanying code at
{\small\url{https://git.io/v7wtW}}.

\subsection{Equivalences}
\label{sec:eq}

Given types {\small\AgdaBound{A}} and {\small\AgdaBound{B}}, a function
{\small\AgdaBound{f}~\AgdaSymbol{:}~\AgdaBound{A}~\AgdaSymbol{→}~\AgdaBound{B}}
is a quasi-inverse, if there is another function
{\small\AgdaBound{g}~\AgdaSymbol{:}~\AgdaBound{B}~\AgdaSymbol{→}~\AgdaBound{A}}
that acts as both a left and right inverse to {\small\AgdaBound{f}}:

\begin{code}
is-qinv : {A B : 𝒰} → (f : A → B) → 𝒰
is-qinv {A} {B} f = Σ[ g ∶ (B → A) ] (g ∘ f ∼ id × f ∘ g ∼ id)
\end{code}

% \VC{Maybe we can split the explanation of contractible and propositions and move
%   it to 3.1?}

In general, for a given ${\small\AgdaBound{f}}$, there could be several
unequal inhabitants of the type
${\small\AgdaFunction{is-qinv}~\AgdaBound{f}}$. As Ch.~4 of the HoTT
book~\cite{hottbook} details, this is problematic in the
proof-relevant setting of HoTT. To ensure that a function
${\small\AgdaBound{f}}$ can be an equivalence in at most one way, an
additional coherence condition is added to quasi-inverses to define
\emph{half adjoint equivalences}:

\begin{code}
is-hae : {A B : 𝒰} → (f : A → B) → 𝒰
is-hae {A} {B} f = Σ[ g ∶ (B → A) ] Σ[ η ∶ g ∘ f ∼ id ] Σ[ ε ∶ f ∘ g ∼ id ] (ap f ∘ η ∼ ε ∘ f)

qinv-is-hae : {A B : 𝒰} {f : A → B} → is-qinv f → is-hae f
\end{code}
\AgdaHide{
\begin{code}
qinv-is-hae = {!!}
\end{code}
}

Using this latter notion, we can define a well-behaved notion of
equivalences between two types:

\begin{code}
is-equiv = is-hae

_≃_ : (A B : 𝒰) → 𝒰
A ≃ B = Σ[ f ∶ (A → B) ] (is-equiv f)
\end{code}

It is straightforward to lift paths to equivalences as shown below:

% \jacques{But transport does not occur below at all, not even
% implicitly.  In fact, the 4 functions below are so trivial that
% they could be collapsed into 1 without loss of comprehension.
% Compared to how complex a lot of the rest of this is (such as
% the previous sub-section), what's the point of taking so much
% space with this?}

\AgdaHide{
\begin{code}
idh : {A : 𝒰} {P : A → 𝒰} → (f : Π[ a ∶ A ] P a) → f ∼ f
idh f a = refl (f a)
\end{code}
}

\begin{code}
ide : (A : 𝒰) → A ≃ A
ide A = id , id , refl , refl , (refl ∘ refl)

transport-equiv : {A : 𝒰} (P : A → 𝒰) → {a b : A} → a == b → P a ≃ P b
transport-equiv P (refl a) = ide (P a)

id-to-equiv : {A B : 𝒰} → A == B → A ≃ B
id-to-equiv = transport-equiv id
\end{code}

Dually, univalence allows us to construct paths from equivalences. We postulate
univalence as an axiom in our Agda library:

\begin{code}
postulate
  univalence : (A B : 𝒰) → is-equiv (id-to-equiv {A} {B})
\end{code}

We also give a short form {\small\AgdaFunction{ua}} for getting a path from an
equivalence, and prove some computation rules for it:

\begin{code}
module _ {A B : 𝒰} where
  ua : A ≃ B → A == B
  ua = pr₁ (univalence A B)

  ua-β : id-to-equiv ∘ ua ∼ id
  ua-β = pr₁ (pr₂ (pr₂ (univalence A B)))

  ua-β₁ : transport id ∘ ua ∼ pr₁
  ua-β₁ eqv = transport _ (ua-β eqv) (ap pr₁)

  ua-η : ua ∘ id-to-equiv ∼ id
  ua-η = pr₁ (pr₂ (univalence A B))
\end{code}

\subsection{Propositional Truncation}

A type {\small\AgdaBound{A}} is \emph{contractible} (h-level 0 or
(-2)-truncated), if it has a center of contraction, and all other
terms of {\small\AgdaBound{A}} are connected to it by a path:

%% \VC{FIXME: Σ and Π are rendered in different colors}
%% \amr{one is a record and one is a function. Ok I guess}

\begin{code}
is-contr : (A : 𝒰) → 𝒰
is-contr A = Σ[ a ∶ A ] Π[ b ∶ A ] (a == b)
\end{code}

As alluded to in the previous section, equivalences are contractible
(4.2.13 in~\cite{hottbook}):

\begin{code}
is-equiv-is-contr : {A B : 𝒰} {f : A → B} → is-equiv f → is-contr (is-equiv f)
\end{code}
\AgdaHide{
\begin{code}
is-equiv-is-contr = {!!}
\end{code}
}

A type {\small\AgdaBound{A}} is a \emph{proposition} (h-level 1 or
(-1)-truncated) if all pairs of terms of {\small\AgdaBound{A}} are
connected by a path. Such a type can have at most one inhabitant; it is
``contractible if inhabited.'' Finally, a type {\small\AgdaBound{A}} is
a \emph{set} if for any two terms {\small\AgdaBound{a}} and
{\small\AgdaBound{b}} of {\small\AgdaBound{A}}, its type of paths
{\small\AgdaBound{a}~\AgdaFunction{==}~\AgdaBound{b}} is a proposition:

\begin{code}
is-prop : (A : 𝒰) → 𝒰
is-prop A = Π[ a ∶ A ] Π[ b ∶ A ] (a == b)

is-set : (A : 𝒰) → 𝒰
is-set A = Π[ a ∶ A ] Π[ b ∶ A ] is-prop (a == b)
\end{code}

Any type can be truncated to a proposition by freely adding
paths. This is the propositional truncation (or (-1)-truncation) which
can be expressed as a higher inductive type (HIT). The type
constructor {\small\AgdaInductiveConstructor{∥\_∥}} takes a type
{\small\AgdaBound{A}} as a parameter; the point constructor
{\small\AgdaInductiveConstructor{∣\_∣}} coerces terms of type
{\small\AgdaBound{A}} to terms in the truncation; and the path
constructor {\small\AgdaInductiveConstructor{ident}} identifies any
two points in the truncation, making it a proposition. We must do this
as a {\small\AgdaKeyword{postulate}} as Agda does not yet support
HITs:

\begin{code}
postulate
    ∥_∥    : (A : 𝒰) → 𝒰
    ∣_∣    : {A : 𝒰} → (a : A) → ∥ A ∥
    ident  : {A : 𝒰} {a b : ∥ A ∥} → a == b

∥-∥-is-prop : {A : 𝒰} → is-prop ∥ A ∥
∥-∥-is-prop _ _ = ident
\end{code}

This makes
{\small\AgdaInductiveConstructor{∥}\AgdaBound{A}\AgdaInductiveConstructor{∥}}
the ``free'' proposition on any type {\small\AgdaBound{A}}. The
recursion principle (below) ensures that we can only eliminate a
propositional truncation to a type that is a proposition:

\begin{code}
module _ {A : 𝒰} (P : 𝒰) (f : A → P) (φ : is-prop P) where
  postulate
    rec-∥-∥ : ∥ A ∥ → P
    rec-∥-∥-β : Π[ a ∶ A ] (rec-∥-∥ ∣ a ∣ == f a)
\end{code}

\begin{figure}
\begin{tabular}{c@{\qquad\qquad}c}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]]
  \draw (0,-5) ellipse (2cm and 0.8cm);
  \node[below] at (0,-6) {Base Space $A$};
  \draw[fill] (-1,-5) circle [radius=0.025];
  \node[below] at (-1,-5) {$x$};
  \draw[fill] (1,-5) circle [radius=0.025];
  \node[below] at (1,-5) {$y$};
  \draw (-1,-2) ellipse (0.5cm and 2cm);
  \node[left] at (-1.5,-2) {Fiber $P(x)$};
  \draw (1,-2) ellipse (0.5cm and 2cm);
  \node[right] at (1.5,-2) {Fiber $P(y)$};
\end{tikzpicture}
&
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]]
  \draw (0,-5) ellipse (2cm and 0.8cm);
  \node[below] at (0,-6) {Base Space $A$};
  \draw[fill] (-1,-5) circle [radius=0.025];
  \node[below] at (-1,-5) {$x$};
  \draw[fill] (1,-5) circle [radius=0.025];
  \node[below] at (1,-5) {$y$};
  \draw (-1.3,-2) ellipse (0.5cm and 2cm);
  \node[left] at (-1.8,-2) {Fiber $P(x)$};
  \draw (1.3,-2) ellipse (0.5cm and 2cm);
  \node[right] at (1.8,-2) {Fiber $P(y)$};
  \draw[below,cyan,thick] (-1,-5) -- (1,-5);
  \node[below,cyan,thick] at (0,-5) {$==$};
  \draw[->,red,thick] (-0.8,-1.7) to [out=45, in=135] (0.8,-1.7);
  \draw[->,red,thick] (0.8,-2.3) to [out=-135, in=-45] (-0.8,-2.3);
  \node[red,thick] at (0,-2) {$\simeq$};
\end{tikzpicture}
\end{tabular}
\caption{\label{fig:fib}(left) Type family $P : A \rightarrow \mathcal{U}$ as a
  fibration with total space $\Sigma_{(x:A)} P(x)$;\newline
 (right) a path $x == y$
  in the base space induces an equivalence between the spaces (fibers)
  $P(x)$ and $P(y)$}
\end{figure}

\subsection{Type Families are Fibrations}

As illustrated in Fig.~\ref{fig:fib}, a type family
{\small\AgdaBound{P}} over a type~{\small\AgdaBound{A}} is a fibration
with base space~{\small\AgdaBound{A}}, with every
{\small\AgdaBound{x}} in {\small\AgdaBound{A}} inducing a fiber
{\small\AgdaBound{P}~\AgdaBound{x}}, and with total space
{\small\AgdaPrimitiveType{Σ[}~\AgdaBound{x}~\AgdaSymbol{∶}~\AgdaBound{A}~\AgdaSymbol{]}~\AgdaSymbol{(}\AgdaBound{P}~\AgdaBound{x}\AgdaSymbol{)}}.\footnote{In
this and following figures, we color paths in blue and functions
in red.}

The path lifting property mapping a path in the base space to a path
in the total space can be defined as follows:

\begin{code}
lift : {A : 𝒰} {P : A → 𝒰} {x y : A} → (u : P x) (p : x == y) → (x , u) == (y , transport P p u)
lift u (refl x) = refl (x , u)
\end{code}

As illustrated in the figure below, the point
{\small\AgdaFunction{transport}~\AgdaBound{P}~\AgdaBound{p}~\AgdaBound{u}}
is in the space {\small\AgdaBound{P}~\AgdaBound{y}}. A path from that
point to another point {\small\AgdaBound{v}} in
{\small\AgdaBound{P}~\AgdaBound{y}} can be viewed as a virtual
``path'' between {\small\AgdaBound{u}} and {\small\AgdaBound{v}} that
``lies over'' {\small\AgdaBound{p}}. Following Licata and
Brunerie~\cite{licata2015cubical}, we often use the syntax
{\small\AgdaBound{u} \AgdaFunction{==} \AgdaBound{v} \AgdaFunction{[}
  \AgdaBound{P} \AgdaFunction{↓} \AgdaBound{p} \AgdaFunction{]}} for
the path
{\small\AgdaFunction{transport}~\AgdaBound{P}~\AgdaBound{p}~\AgdaBound{u}
  \AgdaFunction{==} \AgdaBound{v}} to reinforce this perspective. In
other words, the curved ``path'' between {\small\AgdaBound{u}} and
{\small\AgdaBound{v}} below consists of first transporting
{\small\AgdaBound{u}} to the space {\small\AgdaBound{P}~\AgdaBound{y}}
along {\small\AgdaBound{p}} and then following the straight path in
{\small\AgdaBound{P}~\AgdaBound{y}} to {\small\AgdaBound{v}}:

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]]
  \draw (-3,0) ellipse (1.5cm and 2.5cm);
  \draw (3,2) ellipse (2cm and 1.5cm);
  \draw (3,-2) ellipse (2cm and 1.5cm);
  \node[blue,thick,above] at (-3,3) {$A$};
  \node[blue,thick,above] at (3.3,3.7) {$P(x)$};
  \node[blue,thick,below] at (3.3,-3.7) {$P(y)$};
  \draw[fill] (-3,1.5) circle [radius=0.025];
  \draw[fill] (-3,-1.5) circle [radius=0.025];
  \draw[left,cyan,thick] (-3,1.5) -- (-3,-1.5);
  \node[left] (X) at (-3,1.5) {$x$};
  \node[left] at (-3,-1.5) {$y$};
  \draw[fill] (3,-1.7) circle [radius=0.025];
  \draw[fill] (3,2) circle [radius=0.025];
  \node[above] at (3,2) {$u$};
  \draw[fill] (3,-2.8) circle [radius=0.025];
  \node[below] at (3,-2.8) {$v$};
  \node[left,above] at (3,-1.7) {$\!\!\!\AgdaFunction{transport}~\AgdaFunction{P}~\AgdaFunction{p}~\AgdaFunction{u}$};
  \node[left,cyan] at (-3,0) {$p$};
  \draw[->,red,thick] (3,1.8) -- (3,-1.2);
  \draw[->,red,dashed,thick] (-3,1.5) to [out=45, in=135] (1.15,2.5);
  \draw[->,red,dashed,thick] (-3,-1.5) to [out=-45, in=-135] (1.15,-2.5);
  %%
  \draw[cyan,thick] (3,-1.7) to (3,-2.8);
  \draw[cyan,dashed,thick] (3,2) to [out=5, in=-5] (3,-2.8);
\end{tikzpicture}
\end{center}

\noindent Given a fibration ${\small\AgdaBound{P}}$ and points
{\small\AgdaBound{x}}, {\small\AgdaBound{y}}, {\small\AgdaBound{u}}, and
{\small\AgdaBound{v}} as above, we have the following characterization of
dependent paths in the total space:

\begin{code}
module _ {A : 𝒰} {P : A → 𝒰} {x y : A} {u : P x} {v : P y} where

  dpair= : Σ[ p ∶ x == y ] (u == v [ P ↓ p ]) → (x , u) == (y , v)
  dpair= (refl x , refl u) = refl (x , u)

  dpair=-β : (w : Σ[ p ∶ x == y ] (u == v [ P ↓ p ])) → (ap pr₁ ∘ dpair=) w == pr₁ w
  dpair=-β (refl x , refl u) = refl (refl x)

  dpair=-e : (x , u) == (y , v) → x == y
  dpair=-e = ap pr₁
\end{code}

\AgdaHide{
\begin{code}
prop-is-set : {A : 𝒰} → is-prop A → is-set A
prop-is-set φ a b p q = {!!}

is-equiv-is-prop : {A B : 𝒰} {f : A → B} → is-prop (is-equiv f)
is-equiv-is-prop = {!!}

eqv= : {A B : 𝒰} {eqv eqv' : A ≃ B} → (pr₁ eqv == pr₁ eqv') → eqv == eqv'
eqv= φ = dpair= (φ , is-equiv-is-prop _ _)
\end{code}
}

The first function builds a path in the total space given a path between
{\small\AgdaBound{u}} and {\small\AgdaBound{v}} that lies over a path
{\small\AgdaBound{p}} in the base space; the second function is a computation
rule for this path; and the third function eliminates a path in the total space
to a path in the base space.

\subsection{Univalent Fibrations}

Univalent fibrations are defined by Kapulkin and
Lumsdaine~\cite{SimplicialModel} in the simplicial set (sSet) model.  In
our context, a type family (fibration)
{\small\AgdaBound{P}~\AgdaSymbol{:}~\AgdaBound{A}~\AgdaSymbol{→}~\AgdaFunction{𝒰}}
is univalent if the map
{\small\AgdaFunction{transport-equiv}~\AgdaBound{P}} defined in
Sec.~\ref{sec:eq} is an equivalence, that is, if the space of paths in
the base space is \emph{equivalent} to the space of equivalences between
the corresponding fibers. Fig.~\ref{fig:fib} (right) illustrates the
situation: we know that for any fibration {\small\AgdaBound{P}} that a
path~{\small\AgdaBound{p}} in the base space induces via
{\small\AgdaFunction{transport-equiv}~\AgdaBound{P}~\AgdaBound{p}} an
equivalence between the fibers. For a fibration to be univalent, the
reverse must also be true: every equivalence between the fibers must
induce a path in the base space. Formally, we have the following
definition:

\begin{code}
is-univ-fib : {A : 𝒰} (P : A → 𝒰) → 𝒰
is-univ-fib {A} P = ∀ (a b : A) → is-equiv (transport-equiv P {a} {b})
\end{code}

We note that the univalence axiom (for {\small\AgdaFunction{𝒰}}) is a
specialization of {\small\AgdaFunction{is-univ-fib}} to the identity
fibration, {\small\AgdaFunction{id}}. More generally, we can define
universes \`{a} la Tarski by having a code {\small\AgdaFunction{U}} for
the universe and an interpretation function {\small\AgdaFunction{El}}
into {\small\AgdaFunction{𝒰}}. Such a presented universe is univalent if
{\small\AgdaFunction{El}} is a univalent fibration:

\begin{code}
Ũ = Σ[ U ∶ 𝒰 ] (U → 𝒰)

is-univalent : Ũ → 𝒰
is-univalent (U , El) = is-univ-fib El
\end{code}

\noindent As Christensen~\cite{christensen} explains, a type
{\small\AgdaBound{U}} is \emph{rarely} the base of a univalent
fibration. Yet, in that same paper, Christensen characterizes a class
of types that is always the base of univalent fibrations. We explain
this point and exploit it to build a custom univalent subuniverse in
the next section.

%% \VC{We never use is-univalent later, so might as well just delete it}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{The Subuniverse {\normalfont\AgdaFunction{Ũ[} \AgdaDatatype{𝟚} \AgdaFunction{]}}}
\label{sec:model}

We now have all the ingredients necessary to define the class of
univalent subuniverses we are interested in. Given any type
{\small\AgdaBound{T}}, we can build a propositional predicate that
picks out from among all the types in the universe exactly those which
are identified with~{\small\AgdaBound{T}}. This lets us build up a
``singleton'' subuniverse of~{\small\AgdaFunction{𝒰}} as follows:

\begin{code}
Ũ[_] : (T : 𝒰) → Ũ
Ũ[ T ] = U , El
  where
    U   = Σ[ X ∶ 𝒰 ] ∥ X == T ∥
    El  = pr₁
\end{code}

We will prove in this section and the next that choosing
{\small\AgdaBound{T}} to be {\small\AgdaDatatype{𝟚}} produces a
universe that is sound and complete with respect to the language
$\PiTwo$. The bulk of the argument consists of establishing that
{\small\AgdaFunction{Ũ[} \AgdaDatatype{𝟚} \AgdaFunction{]}} is a
univalent universe. We focus on this argument in the first subsection.
In the next two subsections, we use this result to characterize the
points and paths in the type of codes for this universe. In
Sec.~\ref{sec:correspondence} this characterization of points and
paths will be shown to match the types and combinators of $\PiTwo$.

% \jacques{Below is where we use the univalence of the universe
% 𝒰, in a crucial way, to show that the fibration El𝟚 associated
% to the sub-universe is univalent.  This is indeed {\bf not}
% circular, but may appear un-interesting!  One of the things that
% we have lost in this paper is the text saying that most
% fibrations, even in a univalent universe, are not univalent.
% Without that, this result seems very hollow.}

\subsection{The Fibration {\normalfont\AgdaFunction{El𝟚}} is Univalent}

The universe {\small\AgdaFunction{Ũ[} \AgdaDatatype{𝟚}
  \AgdaFunction{]}} consists of a base space
{\small\AgdaFunction{U[𝟚]}} of the codes for the elements, and an
interpretation function {\small\AgdaFunction{El𝟚}}, defined as follows:

\begin{code}
U[𝟚] : 𝒰
U[𝟚]  = pr₁ Ũ[ 𝟚 ]   -----  = Σ[ X ∶ 𝒰 ] ∥ X == 𝟚 ∥

El𝟚  : Σ[ X ∶ 𝒰 ] ∥ X == 𝟚 ∥ → 𝒰
El𝟚  = pr₁
\end{code}

The type family {\small\AgdaFunction{El𝟚}} defines a fibration with
base space {\small\AgdaFunction{U[𝟚]}} as shown below:

\begin{center}
\begin{tikzpicture}[scale=0.8,every node/.style={scale=0.8}]]
  \draw (0,-5) ellipse (3.5cm and 1.2cm);
  \node[below] at (0,-6.3) {Base Space \AgdaFunction{U[𝟚]} = \AgdaRecord{Σ[} \AgdaBound{X} \AgdaRecord{∶} \AgdaFunction{𝒰} \AgdaRecord{]} \AgdaPostulate{∥} \AgdaBound{X} \AgdaDatatype{==} \AgdaDatatype{𝟚} \AgdaPostulate{∥}};
  \draw[fill] (-2,-4.75) circle [radius=0.025];
  \node[below] at (-2,-4.75) {\AgdaSymbol{(}\AgdaDatatype{𝟚}~\AgdaSymbol{,}~\AgdaInductiveConstructor{∣refl}~\AgdaDatatype{𝟚}\AgdaInductiveConstructor{∣}\AgdaSymbol{)}};
  \draw[fill] (2,-4.75) circle [radius=0.025];
  \node[below] at (2,-4.75) {\AgdaSymbol{(}\AgdaBound{X}~\AgdaSymbol{,}~\AgdaInductiveConstructor{∣}\AgdaBound{p}\AgdaInductiveConstructor{∣}\AgdaSymbol{)}};
  \draw[below,cyan,thick] (-2,-4.75) -- (2,-4.75);
  \node[below,cyan,thick] at (0,-4.75) {\AgdaDatatype{==}};

  \draw (-2,-2) ellipse (0.5cm and 1cm);
  \node[left] at (-2.5,-2) {Fiber \AgdaDatatype{𝟚}};
  \draw (2,-2) ellipse (0.5cm and 1cm);
  \node[right] at (2.5,-2) {Fiber \AgdaBound{X}};
  \draw[->,red,thick] (-1.5,-1.7) to [out=45, in=135] (1.5,-1.7);
  \draw[->,red,thick] (1.5,-2.3) to [out=-135, in=-45] (-1.5,-2.3);
  \node[red,thick] at (0,-2) {$\simeq$};
\end{tikzpicture}
\end{center}

Our goal is to show that {\small\AgdaFunction{El𝟚}} is a univalent
fibration. We establish this by chaining two equivalences. The first
equivalence is a simple appeal to univalence in order to establish that
{\small (\AgdaBound{X}~\AgdaFunction{==}~\AgdaDatatype{𝟚})
  ~\AgdaFunction{≃}~ (\AgdaBound{X}~\AgdaFunction{≃}~\AgdaDatatype{𝟚})},
i.e., our base space is equivalent to the space
\mbox{\small\AgdaRecord{Σ[} ~\AgdaBound{X} ~\AgdaRecord{∶}
  ~\AgdaFunction{𝒰}~ \AgdaRecord{]} ~\AgdaPostulate{∥} ~\AgdaBound{X}
  ~\AgdaFunction{≃}~ \AgdaDatatype{𝟚} ~\AgdaPostulate{∥}}.  We name this
space {\small\AgdaFunction{BAut}~\AgdaDatatype{𝟚}}. Generally,
{\small\AgdaFunction{BAut}~\AgdaBound{T}} is the ``classifying space''
of all types that are (merely) equivalent to {\small\AgdaBound{T}}.  The
second equivalence consists of proving that the first projection on
{\small\AgdaFunction{BAut}~\AgdaDatatype{T}} is in fact a univalent
fibration, for all spaces with shape \mbox{\small\AgdaRecord{Σ[}
  ~\AgdaBound{X} ~\AgdaRecord{∶} ~\AgdaFunction{𝒰}~ \AgdaRecord{]}
  ~\AgdaPostulate{∥} ~\AgdaBound{X} ~\AgdaFunction{≃}~ \AgdaDatatype{T}
  ~\AgdaPostulate{∥}} for any type {\small\AgdaDatatype{T}}.  This is
the lemma {\small\AgdaFunction{is-univ-fib-ElB}} below whose original
formulation is due to Christensen~\cite{christensen}:

\begin{code}
BAut : (T : 𝒰) → 𝒰
BAut T = Σ[ X ∶ 𝒰 ] ∥ X ≃ T ∥

ElB : {T : 𝒰} → BAut T → 𝒰
ElB = pr₁

transport-equiv-ElB : {T : 𝒰} {v w : BAut T} (p : v == w)
                    → pr₁ (transport-equiv ElB p) == transport id (dpair=-e p)
transport-equiv-ElB (refl v) = refl id

is-univ-fib-ElB : {T : 𝒰} → is-univ-fib ElB
is-univ-fib-ElB (T , q) (T' , q') = qinv-is-hae (g , η , ε)
  where  g : T ≃ T' → T , q == T' , q'
         g eqv = dpair= (ua eqv , ident)

         η : g ∘ transport-equiv ElB ∼ id
         η (refl ._) = ap dpair=   (dpair= ( ua-η (refl _)
                                   , prop-is-set (λ _ _ → ident) _ _ _ _))

         ε : transport-equiv ElB ∘ g ∼ id
         ε eqv = eqv=  (transport-equiv-ElB (dpair= (ua eqv , ident))
                       ◾ ap (transport id) (dpair=-β (ua eqv , ident))
                       ◾ ua-β₁ eqv )
\end{code}

This establishes that {\small\AgdaFunction{El𝟚}} is a univalent
fibration, giving us a characterization of paths in
{\small\AgdaFunction{U[𝟚]}} in terms of equivalences on booleans which
we exploit next.

\subsection{The Base Space {\normalfont\AgdaFunction{U[𝟚]}}}

The points in the base space {\small\AgdaFunction{U[𝟚]}} are all of
the form
{\small\AgdaSymbol{(}\AgdaBound{X}~\AgdaSymbol{,}~\AgdaInductiveConstructor{∣}\AgdaBound{p}\AgdaInductiveConstructor{∣}\AgdaSymbol{)}}
where {\small\AgdaBound{p}} is of type
{\small\AgdaBound{X}~\AgdaDatatype{==}~\AgdaDatatype{𝟚}}. We evidently
have a canonical point {\small\AgdaFunction{𝟚₀}}:

\begin{code}
𝟚₀  : U[𝟚]
𝟚₀  = (𝟚 , ∣ refl 𝟚 ∣)
\end{code}

which directly corresponds to the boolean type in $\PiTwo$. We remind
the reader that, by construction, {\small\AgdaFunction{U[𝟚]}} is
path-connected.  What remains is to characterize the 1-paths, 2-paths,
and possibly higher paths in {\small\AgdaFunction{U[𝟚]}} and to relate
them to the 1-combinators, 2-combinators, etc. in $\PiTwo$.

To conveniently refer to the paths in {\small\AgdaFunction{U[𝟚]}}, we
define the loop space on a (pointed) type, and show that the loop
space on {\small\AgdaFunction{BAut}~\AgdaDatatype{𝟚}} is equivalent to
{\small\AgdaDatatype{𝟚}~\AgdaFunction{≃}~\AgdaDatatype{𝟚}}:

\begin{code}
Ω : Σ[ T ∶ 𝒰 ] T → 𝒰
Ω (T , t₀) = t₀ == t₀

Aut : (T : 𝒰) → 𝒰
Aut T = T ≃ T

b₀ : {T : 𝒰} → BAut T
b₀ {T} = T , ∣ ide T ∣

ΩBAut≃Aut[_] : (T : 𝒰) → Ω (BAut T , b₀) ≃ Aut T
ΩBAut≃Aut[ T ] = transport-equiv ElB , is-univ-fib-ElB b₀ b₀
\end{code}

The above results states that, in general, the loop space of the
classifying space of a type {\small\AgdaBound{T}} is equivalent to the
type of automorphisms of {\small\AgdaBound{T}}.  In particular, it
follows that
{\small\AgdaFunction{Ω}~\AgdaSymbol{(}\AgdaFunction{BAut}~\AgdaDatatype{𝟚}
  \AgdaInductiveConstructor{,} \AgdaFunction{𝟚₀}\AgdaSymbol{)}
  \AgdaFunction{≃} \AgdaFunction{Aut} \AgdaDatatype{𝟚}} which reduces
the problem of characterizing paths on {\small\AgdaFunction{U[𝟚]}} to
the much simpler problem of characterizing automorphisms on the type
of booleans.  We now turn our attention to solving that problem.

% In HoTT, types are higher groupoids, and $∞$Grpd is the $(∞,1)$-topos
% of $∞$-groupoids, of which HoTT is an internal language. For an object
% $T$, we can define an $∞$-groupoid of $T$s, with objects $T$s,
% morphisms equivalences between $T$s, and so on. This is a full
% sub-$∞$-groupoid of $∞$Grpd, and gives the classifying space for
% spaces equivalent to $T$s. This is denoted by the type
% {\small\AgdaFunction{BAut}~\AgdaBound{T}}. The notation is suggestive of the
% fact that it corresponds classically to the delooping group of the
% automorphism group. We truncate to a ``mere equivalence'' so that the
% choice of the specific equivalence is impertinent.

%% Since equivalences are preserved over dependent sum and propositional truncation, so we have
%% {\small\AgdaFunction{Ω (Ũ , 𝟚₀) ≃ Ω (BAut(𝟚) , b₀)}}

% As a consequence, we have that the loop space of
% {\small\AgdaFunction{BAut}~\AgdaBound{T}} is equivalent to
% {\small\AgdaFunction{Aut}~\AgdaBound{T}}:

%It remains to check that {\small\AgdaFunction{BAut}~\AgdaBound{T}} is the same
%as our singleton universe
%{\small\AgdaFunction{Ũ[}\AgdaBound{T}\AgdaFunction{]}}. This follows by
%univalence and the universal property of truncation.

\AgdaHide{
% Only show this if you will provide the proof - otherwise the
% statement is already in the paragraph above.
\begin{code}
BAut≃Ũ[_] : (T : 𝒰) → BAut T ≃ pr₁ Ũ[ T ]
BAut≃Ũ[ T ] = {!!}
\end{code}
}

%% Instantiating the lemma from the previous section with \AgdaFunction{𝟚}, we have
%% that {\small\AgdaFunction{Ũ[𝟚]}} is a univalent subuniverse, with \AgdaFunction{pr₁} the
%% univalent fibration. By the property of being a univalent fibration we have that
%% {\small\AgdaFunction{Ω (BAut(𝟚) , 𝟚₀) ≃ (𝟚 ≃ 𝟚)}}.

\subsection{Automorphisms on {\normalfont\AgdaDatatype{𝟚}}}

The type {\small\AgdaFunction{𝟚}} has two point constructors, and no
path constructors, which means it has no non-trivial paths on its
points except {\small\AgdaFunction{refl}}. In fact, we can prove in
intensional type theory using large elimination, that the two
constructors are disjoint. This is reflected in the absurd pattern
when using dependent pattern matching in Agda. More generally,
{\small\AgdaFunction{𝟚 ≃ 𝟙 ⊎ 𝟙}} and the disjoint union of two sets is
a set:

\begin{code}
0₂≠1₂ : 0₂ == 1₂ → ⊥
0₂≠1₂ p = transport code p tt
  where  code : 𝟚 → 𝒰
         code 0₂ = ⊤
         code 1₂ = ⊥
\end{code}

Using {\small\AgdaFunction{0₂≠1₂}} and function extensionality
(derivable from univalence) we can prove that there are exactly two
different equivalences between {\small\AgdaFunction{𝟚}} and
{\small\AgdaFunction{𝟚}}.  Furthermore, for any equivalence
{\small\AgdaFunction{f}}, using the fact that
{\small\AgdaFunction{is-equiv f}} is a proposition, we can show that
there are exactly two inhabitants of {\small\AgdaFunction{𝟚 ≃ 𝟚}}:

\begin{code}
id≃ not≃ : 𝟚 ≃ 𝟚
id≃   = id  , qinv-is-hae (id , refl , refl)
not≃  = not , qinv-is-hae (not , (λ {0₂ → refl 0₂ ; 1₂ → refl 1₂})
                               , (λ {0₂ → refl 0₂ ; 1₂ → refl 1₂}))
  where  not : 𝟚 → 𝟚
         not 0₂ = 1₂
         not 1₂ = 0₂
\end{code}

Here something very special happens: although in general the type
formed by taking~$n$ disjoint unions of {\small\AgdaFunction{𝟙}} has a
space of automorphisms of size $n!$, in our case we have that
{\small\AgdaFunction{𝟚}} and {\small\AgdaFunction{𝟚 ≃ 𝟚}} are of the
same size. This combinatorial accident can actually be lifted to show
that there is an equivalence between {\small\AgdaFunction{𝟚 ≃ 𝟚}} and
{\small\AgdaFunction{𝟚}}.  By composing the chain of equivalences
{\small\AgdaFunction{Ω (Ũ , 𝟚₀) ≃ Ω (BAut(𝟚) , b₀) ≃ (𝟚 ≃ 𝟚) ≃ 𝟚}} we
obtain:

\AgdaHide{\begin{code}
postulate
\end{code}}

\begin{code}
  𝟚≃Ω𝟚₀ : 𝟚 ≃ (𝟚₀ == 𝟚₀)
\end{code}

Thus there are only two distinct 1-loops in
{\small\AgdaFunction{U[𝟚]}}. Calling them {\small\AgdaFunction{id𝟚}}
and {\small\AgdaFunction{not𝟚}}, we obtain a decomposition:

\AgdaHide{\begin{code}
id𝟚 : {A : U[𝟚]} → A == A
id𝟚 {A} = refl A

not𝟚 : 𝟚₀ == 𝟚₀
not𝟚 = dpair= (ua not≃ , ident)

postulate
\end{code}}

\begin{code}
  all-1-loops : (p : 𝟚₀ == 𝟚₀) → (p == id𝟚) + (p == not𝟚)
\end{code}

that every loop in {\small\AgdaFunction{U[𝟚]}} is identifiable with
either the identity or boolean negation.

For 2-loops in {\small\AgdaFunction{U[𝟚]}}, the following analysis shows
that they are identifiable with the trivial path. First, by applying the
induction principle for disjoint unions, and path induction, we can
prove {\small\AgdaFunction{𝟚}} is a set:

\begin{code}
𝟚-is-set : is-set 𝟚
𝟚-is-set 0₂ 0₂ (refl .0₂) (refl .0₂) = refl (refl 0₂)
𝟚-is-set 0₂ 1₂ ()
𝟚-is-set 1₂ 0₂ ()
𝟚-is-set 1₂ 1₂ (refl .1₂) (refl .1₂) = refl (refl 1₂)
\end{code}

From this, we obtain that {\small\AgdaFunction{𝟚₀ == 𝟚₀}} is also a
set by using {\small\AgdaFunction{ua}} and
{\small\AgdaFunction{transport}}. This in turns shows the
contractibility of 2-loops:

\begin{code}
Ω𝟚₀-is-set : is-set (𝟚₀ == 𝟚₀)
Ω𝟚₀-is-set = transport is-set (ua 𝟚≃Ω𝟚₀) 𝟚-is-set

all-2-loops : {p : 𝟚₀ == 𝟚₀} → (γ : p == p) → γ == refl p
all-2-loops {p} γ = Ω𝟚₀-is-set p p γ (refl p)
\end{code}

In the next section, we will use {\small\AgdaFunction{all-1-loops}}
and {\small\AgdaFunction{all-2-loops}} as crucial ingredients for
showing the correspondence between {\small\AgdaFunction{U[𝟚]}} and
\PiTwo.

Note that most of the results in this section are generic.  However
when we move beyond {\small\AgdaFunction{𝟚}}, the combinatorial
explosion of the path space is such that explicit enumeration quickly
becomes impractical, and other techniques will become necessary.

%% With a syntactic presentation of \AgdaSymbol{Ω(BAut(𝟚))},
%% we get all the automorphisms on \AgdaSymbol{𝟚}, which gives a complete model for
%% \PiTwo.

%% However, the problem is easier for \AgdaSymbol{𝟚}, because
%% \AgdaSymbol{Aut(𝟚) ≃ 𝟚}, which gives the following easy lemmas for
%% 1-paths and 2-paths on \AgdaSymbol{𝟚}: \AgdaSymbol{all-1-loops} and
%% \AgdaSymbol{all-2-loops}.

% In previous work on $\Pi$ we noted a possible connection with HoTT:
% \begin{quote}
%   It is, therefore, at least plausible that a variant of HoTT based exclusively
%   on reversible functions that directly correspond to equivalences would have
%   better computational properties. Our current result is a step, albeit
%   preliminary, in that direction as it only applies to finite
%   types~\cite{Carette2016}.
% \end{quote}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Correspondence between {\normalfont\AgdaFunction{U[𝟚]}} and \PiTwo}
\label{sec:correspondence}

Formalizing, in a precise sense, the connection between reversible
functions in a programming language and paths in a univalent universe,
as intuitive as it may seem, is rather subtle. Paths in HoTT come
equipped with principles like the ``contractibility of singletons'',
``transport'', and ``path induction'' and none of these principles
seem to have any direct counterpart in the world of reversible
programming. We will however demonstrate how the semantics of an
entire (but admittedly small) reversible programming language such as
$\PiTwo$ can be captured by a specification as compact as
{\small\AgdaRecord{Σ[} \AgdaBound{X} \AgdaRecord{∶} \AgdaFunction{𝒰}
  \AgdaRecord{]} \AgdaPostulate{∥} \AgdaBound{X} \AgdaDatatype{==}
  \AgdaDatatype{𝟚} \AgdaPostulate{∥}}. Our precise correspondence will
consist of building mappings between~\PiTwo{} and
{\small{\AgdaFunction{Ũ[𝟚]}}}, for points, 1-paths, 2-paths, and
3-paths, such that each map is invertible up to the appropriate notion
of equality. This gives a notion of soundness and completeness for
each level.

%% JC: while the next sentence is ``true enough'', this isn't really
%% carried out in full in the code.  So we shouldn't claim it in the
%% paper.
%%\newtext{
%%  The syntactic category of \PiTwo{} forms a 2-groupoid, we construct a
%%  2-functor out of it to Ũ[𝟚] and show that it is an equivalence.
%%}

\subsection{Mappings}

The mappings for points (level-0) are straightforward, as both
{\small\AgdaDatatype{Π₂}} and {\small\AgdaFunction{U[𝟚]}} are
singletons:

\begin{code}
⟦_⟧₀ : Π₂ → U[𝟚]
⟦ `𝟚 ⟧₀ = 𝟚₀

⌜_⌝₀ : U[𝟚] → Π₂
⌜ _ ⌝₀ = `𝟚
\end{code}

Level-1 is the first non-trivial level. To each syntactic combinator
{\small\AgdaFunction{c}~\AgdaSymbol{:}~\AgdaBound{A}~\AgdaDatatype{⟷₁}~\AgdaBound{B}},
we associate a path from
{\small{\AgdaFunction{⟦}~\AgdaBound{A}~\AgdaFunction{⟧₀}}} to
{\small{\AgdaFunction{⟦}~\AgdaBound{B}~\AgdaFunction{⟧₀}}} and
vice-versa. The mapping from the univalent universe back to the syntax
of the reversible language is only possible because we have a complete
characterization of the paths in the universe (captured in the
construction of {\small\AgdaFunction{all-1-loops}} in the previous
section):

\begin{code}
⟦_⟧₁ : {A B : Π₂} → A ⟷₁ B → ⟦ A ⟧₀ == ⟦ B ⟧₀
⟦ `id ⟧₁       = id𝟚
⟦ `not ⟧₁      = not𝟚
⟦ !₁ p ⟧₁      = ! ⟦ p ⟧₁
⟦ p ⊙₁ q ⟧₁    = ⟦ p ⟧₁ ◾ ⟦ q ⟧₁

⌜_⌝₁ : 𝟚₀ == 𝟚₀ → ⌜ 𝟚₀ ⌝₀ ⟷₁ ⌜ 𝟚₀ ⌝₀
⌜ p ⌝₁ with all-1-loops p
... | inl pid   = `id
... | inr pnot  = `not
\end{code}

At level-2, we know by the construction of
{\small\AgdaFunction{all-2-loops}} in the previous section that all
self-paths in the univalent universe are trivial. Nevertheless the
mappings back and forth require quite a bit of (tedious) work. We show
below a few cases of the mapping from 2-combinators to 2-paths and the
full definition of the reverse mapping. In the first direction, it is
a matter of using the necessary properties of paths in the univalent
universe (e.g, each path has an inverse). These properties are proved
by path induction. The reverse direction crucially relies again on the
characterization of 1-loops and the fact that the identity equivalence
and the equivalence that swaps the two booleans are distinct:

\AgdaHide{
\begin{code}
postulate
  !not𝟚=not𝟚 : ! not𝟚 == not𝟚
  id𝟚≠not𝟚 : id𝟚 == not𝟚 → ⊥
\end{code}
}

\begin{AgdaMultiCode}{2}
\begin{code}
⟦_⟧₂ : {A B : Π₂} {p q : A ⟷₁ B} → (u : p ⟷₂ q) → ⟦ p ⟧₁ == ⟦ q ⟧₁
⟦ `id₂ {p = p} ⟧₂   = refl ⟦ p ⟧₁
⟦ !₂ u ⟧₂           = ! ⟦ u ⟧₂
⟦ u₁ ⊙₂ u₂ ⟧₂       = ⟦ u₁ ⟧₂ ◾ ⟦ u₂ ⟧₂
⟦ `idl p ⟧₂         = ◾unitl ⟦ p ⟧₁
⟦ `idr p ⟧₂         = ◾unitr ⟦ p ⟧₁
⟦ `! u ⟧₂           = ap !_ ⟦ u ⟧₂
-- remaining cases are omitted
\end{code}
\AgdaHide{
\begin{code}
⟦ _ ⟧₂              = ?
\end{code}
}
\end{AgdaMultiCode}

\begin{code}
⌜_⌝₂ : {p q : 𝟚₀ == 𝟚₀} → p == q → ⌜ p ⌝₁ ⟷₂ ⌜ q ⌝₁
⌜_⌝₂ {p} {q} u with all-1-loops p | all-1-loops q
... | inl p=id   | inl q=id   = `id₂
... | inl p=id   | inr q=not  = ⊥-elim (id𝟚≠not𝟚 ((! p=id) ◾ u ◾ q=not))
... | inr p=not  | inl q=id   = ⊥-elim (id𝟚≠not𝟚 ((! q=id) ◾ ! u ◾ p=not))
... | inr p=not  | inr q=not  = `id₂
\end{code}

For the final level-3, mapping from the univalent universe to $\PiTwo$
is trivial as the latter has only one constructor at level-3. The
other direction requires some involved reasoning in the univalent
universe to construct the required 3-path:

\begin{code}
lemma : {p q r : 𝟚₀ == 𝟚₀} (p=r : p == r) (q=r : q == r) (u : p == q)
      → u == p=r ◾ ((! p=r) ◾ u ◾ q=r) ◾ (! q=r)

⟦_⟧₃ : {A B : Π₂} {p q : A ⟷₁ B} {u v : p ⟷₂ q} → (α : u ⟷₃ v) → ⟦ u ⟧₂ == ⟦ v ⟧₂
⟦_⟧₃ {`𝟚} {`𝟚} {p} {q} {u} {v} `trunc with all-1-loops ⟦ p ⟧₁ | all-1-loops ⟦ q ⟧₁
... | inl p=id  | inl q=id  =
  lemma p=id q=id ⟦ u ⟧₂
  ◾ ap  (λ x → p=id ◾ x ◾ ! q=id)
         (all-2-loops (! p=id ◾ ⟦ u ⟧₂ ◾ q=id) ◾ ! (all-2-loops (! p=id ◾ ⟦ v ⟧₂ ◾ q=id)))
  ◾ ! (lemma p=id q=id ⟦ v ⟧₂)
... | inl p=id  | inr q=not =  ⊥-elim (id𝟚≠not𝟚 ((! p=id) ◾ ⟦ u ⟧₂ ◾ q=not))
... | inr p=not | inl q=id  =  ⊥-elim (id𝟚≠not𝟚 ((! q=id) ◾ ! ⟦ u ⟧₂ ◾ p=not))
... | inr p=not | inr q=not =
  lemma p=not q=not ⟦ u ⟧₂
  ◾ ap  (λ x → p=not ◾ x ◾ ! q=not)
         (all-2-loops (! p=not ◾ ⟦ u ⟧₂ ◾ q=not) ◾ ! (all-2-loops (! p=not ◾ ⟦ v ⟧₂ ◾ q=not)))
  ◾ ! (lemma p=not q=not ⟦ v ⟧₂)

⌜_⌝₃ : {p q : 𝟚₀ == 𝟚₀} {u v : p == q} → u == v → ⌜ u ⌝₂ ⟷₃ ⌜ v ⌝₂
⌜ _ ⌝₃ = `trunc
\end{code}

\AgdaHide{
\begin{code}
lemma = ?
\end{code}
}

\subsection{Coherence}

It now remains to show that all these mapping are coherent with each
other in the sense that each round trip produces a term that is
identifiable with the original term, effectively showing soundness and
completness of the univalent universe with respect to $\PiTwo$. At
level-0, this is trivial.

At level-1, \emph{soundness} means that the mappings are inverses:
\begin{itemize}
\item any 1-combinator {\small\AgdaBound{p}} mapped to a 1-path and
  back is 2-equivalent to itself, and
\item there is always a 2-path between a 1-path {\small\AgdaBound{p}}
sent to a 1-combinator and back.
\end{itemize}
This is rather more succinct in code:
\begin{code}
⌜⟦_⟧₁⌝₁ : (p : `𝟚 ⟷₁ `𝟚) → p ⟷₂ ⌜ ⟦ p ⟧₁ ⌝₁
⌜⟦ p ⟧₁⌝₁ with canonical p | all-1-loops ⟦ p ⟧₁
... | ID  , p⇔id   | inl p=id   = p⇔id
... | ID  , p⇔id   | inr p=not  = ⊥-elim (id𝟚≠not𝟚 (! ((! p=not) ◾ ⟦ p⇔id ⟧₂)))
... | NOT , p⇔not  | inl p=id   = ⊥-elim (id𝟚≠not𝟚 ((! p=id) ◾ ⟦ p⇔not ⟧₂))
... | NOT , p⇔not  | inr p=not  = p⇔not

⟦⌜_⌝₁⟧₁ : (p : 𝟚₀ == 𝟚₀) → p == ⟦ ⌜ p ⌝₁ ⟧₁
⟦⌜ p ⌝₁⟧₁  with all-1-loops p | canonical ⌜ p ⌝₁
... | inl p=id   | ID  , p⇔id   = p=id
... | inl p=id   | NOT , p⇔not  = ⊥-elim (id𝟚≠not𝟚 ⟦ p⇔not ⟧₂)
... | inr p=not  | ID  , p⇔id   = ⊥-elim (id𝟚≠not𝟚 (! ⟦ p⇔id ⟧₂))
... | inr p=not  | NOT , p⇔not  = p=not
\end{code}

They are also \emph{complete} in the following sense:
\begin{itemize}
\item for any two 1-combinators which map to 1-paths which are
related by a 2-path, the 1-combinators are related by a 2-combinator, and
\item for any two 1-paths which map to 1-combinators which are
related by a 2-combinator these are related by a 2-path.
\end{itemize}
Normally, completeness is a rather difficult result to prove.  But in
our case, the infrastructure from the previous section makes the proof
immediate: For the first proof, the key is \emph{reversibility} of the
level-2 combinators using {\small\AgdaInductiveConstructor{!₂}}; for
the second proof it is the reversibility of paths in the univalent
universe that is critical:

\begin{code}
completeness₁ : {p q : `𝟚 ⟷₁ `𝟚} → ⟦ p ⟧₁ == ⟦ q ⟧₁ → p ⟷₂ q
completeness₁ {p} {q} u = ⌜⟦ p ⟧₁⌝₁ ⊙₂ (⌜ u ⌝₂ ⊙₂ !₂ ⌜⟦ q ⟧₁⌝₁)

completeness₁⁻¹ : {p q : 𝟚₀ == 𝟚₀} → ⌜ p ⌝₁ ⟷₂ ⌜ q ⌝₁ → p == q
completeness₁⁻¹ {p} {q} u = ⟦⌜ p ⌝₁⟧₁ ◾ ⟦ u ⟧₂ ◾ (! ⟦⌜ q ⌝₁⟧₁)
\end{code}

For level-2, the statements are informally quite similar (with all
levels bumped up by one).  For 2-combinators, the result is
trivial. For the other direction starting from 2-paths in the
univalent universe soundness is tricky to even state, mostly because
the types involved in {\small\AgdaFunction{⌜
    ⟦}~\AgdaBound{u}~\AgdaFunction{⟧₂ ⌝₂}} and {\small\AgdaFunction{⟦
    ⌜}~\AgdaBound{u}~\AgdaFunction{⌝₂ ⟧₂}} are non-trivial. But
enumeration of 1-loops reduces the complexity of the problem to
``unwinding'' complex expressions for identity paths:

\begin{code}
⌜⟦_⟧₂⌝₂ :  {p q : `𝟚 ⟷₁ `𝟚}
           (u : p ⟷₂ q) → u ⟷₃ (⌜⟦ p ⟧₁⌝₁ ⊙₂ (⌜ ⟦ u ⟧₂ ⌝₂ ⊙₂ (!₂ ⌜⟦ q ⟧₁⌝₁)))
⌜⟦ u ⟧₂⌝₂ = `trunc

⟦⌜_⌝₂⟧₂ : {p q : 𝟚₀ == 𝟚₀} (u : p == q) → u == ⟦⌜ p ⌝₁⟧₁ ◾ ⟦ ⌜ u ⌝₂ ⟧₂ ◾ (! ⟦⌜ q ⌝₁⟧₁)
⟦⌜_⌝₂⟧₂ {p} {q} u with all-1-loops p | all-1-loops q
... | inl p=id   | inl q=id   =  (lemma p=id q=id u)
                                 ◾ (ap (λ x → p=id ◾ x ◾ ! q=id) (all-2-loops (! p=id ◾ u ◾ q=id)))
... | inl p=id   | inr q=not  = ⊥-elim (id𝟚≠not𝟚 ((! p=id) ◾ u ◾ q=not))
... | inr p=not  | inl q=id   = ⊥-elim (id𝟚≠not𝟚 (! ((! p=not) ◾ u ◾ q=id)))
... | inr p=not  | inr q=not  =  (lemma p=not q=not u)
                                 ◾ (ap (λ x → p=not ◾ x ◾ ! q=not) (all-2-loops (! p=not ◾ u ◾ q=not)))
\end{code}

Level-2 completeness offers no new difficulties:

\begin{code}
completeness₂ : {p q : `𝟚 ⟷₁ `𝟚} {u v : p ⟷₂ q} → ⟦ u ⟧₂ == ⟦ v ⟧₂ → u ⟷₃ v
completeness₂ u = `trunc

completeness₂⁻¹ : {p q : 𝟚₀ == 𝟚₀} {u v : p == q} → ⌜ u ⌝₂ ⟷₃ ⌜ v ⌝₂ → u == v
completeness₂⁻¹ {p} {q} {u} {v} α = ⟦⌜ u ⌝₂⟧₂
                                  ◾ ap (λ x → ⟦⌜ p ⌝₁⟧₁ ◾ x ◾ ! ⟦⌜ q ⌝₁⟧₁) ⟦ α ⟧₃
                                  ◾ (! ⟦⌜ v ⌝₂⟧₂)
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Discussion and Related Work}
\label{sec:discussion}

\paragraph*{Reversible Languages.}
\noindent The practice of programming languages is replete with \emph{ad hoc}
instances of reversible computations: database transactions, mechanisms for data
provenance, checkpoints, stack and exception traces, logs, backups, rollback
recoveries, version control systems, reverse engineering, software transactional
memories, continuations, backtracking search, and multiple-level ``undo''
features in commercial applications. In the early nineties,
Baker~\cite{Baker:1992:LLL,Baker:1992:NFT} argued for a systematic, first-class,
treatment of reversibility. But intensive research in full-fledged reversible
models of computations and reversible programming languages was only sparked by
the discovery of deep connections between physics and
computation~\cite{Landauer:1961,PhysRevA.32.3266,Toffoli:1980,bennett1985fundamental,Frank:1999:REC:930275},
and by the potential for efficient quantum
computation~\cite{springerlink:10.1007/BF02650179}.

The early developments of reversible programming languages started with a
conventional programming language, e.g., an extended $\lambda$-calculus, and either
\begin{enumerate}
\item extended the language with a history
mechanism~\cite{vanTonder:2004,Kluge:1999:SEMCD,lorenz,danos2004reversible}, or
\item imposed constraints on the control flow constructs to make them
reversible~\cite{Yokoyama:2007:RPL:1244381.1244404}.
\end{enumerate}
More modern approaches recognize that reversible programming languages require
a fresh approach and should be designed from first principles without the
detour via conventional irreversible
languages~\cite{Yokoyama:2008:PRP,Mu:2004:ILRC,abramsky2005structural,DiPierro:2006:RCL:1166042.1166047}.

\paragraph*{The $\Pi$ Family of Languages}
\noindent In previous work, Carette, Bowman, James, and
Sabry~\cite{rc2011,James:2012:IE:2103656.2103667,Carette2016}
introduced the~$\Pi$ family of reversible languages based on type
isomorphisms and commutative semiring identities. The fragment without
recursive types is universal for reversible boolean
circuits~\cite{James:2012:IE:2103656.2103667} and the extension with
recursive types and trace
operators~\cite{Hasegawa:1997:RCS:645893.671607} is a Turing-complete
reversible language~\cite{James:2012:IE:2103656.2103667,rc2011}. While
at first sight, $\Pi$ might appear \emph{ad hoc}, it really arises
naturally from an ``extended'' view of the Curry-Howard
correspondence~\cite{Carette2016}: rather than looking at mere
\emph{inhabitation} as the main source of analogy between logic and
computation, \emph{type equivalences} becomes the source of analogy.
This allows one to see an analogy between algebra and reversible
computation.  Furthermore, this works at multiple levels: that of
$1$-algebra (types form a semiring under isomorphism), but also
$2$-algebra (types and equivalences form a weak Rig Groupoid).  In
other words, by taking ``weak Rig Groupoid'' as the starting
semantics, one naturally gets $\Pi$ as the syntax for the language of
proofs of isomorphisms -- in the same way that many terms of the
$\lambda$-calculus arise from Cartesian Closed Categories.

One can also flip this around, and use the $\lambda$-calculus as the
internal language for Cartesian Closed Categories.  However, as
Shulman explains well in his draft book on approaching Categorical
Logic via Type Theory~\cite{shulman}, this works for many other kinds
of categories.  As we are interested in \emph{reversibility}, it is
most natural to look at Groupoids.  Thus $\PiTwo$ represents the
simplest non-trivial case of a (reversible) programming language
distilled from such ideas.

What is more surprising is how this also turns out to be a sound
and complete language for describing the univalent universe
{\small\AgdaFunction{U[𝟚]}}.

\paragraph*{The infinite real projective space $\mathbf{RP}^∞$}
\noindent Buchholtz and Rijke~\cite{buchholtz2017real} use the ``type
of two element sets,'' {\small\AgdaRecord{Σ[} \AgdaBound{X}
  \AgdaRecord{∶} \AgdaFunction{𝒰} \AgdaRecord{]} \AgdaPostulate{∥}
  \AgdaBound{X} \AgdaDatatype{==} \AgdaDatatype{𝕊⁰}
  \AgdaPostulate{∥}}, where~{\small\AgdaDatatype{𝕊⁰}} is the 0-sphere,
or the 0-iterated suspension of {\small\AgdaDatatype{𝟚}}, that is,
{\small\AgdaDatatype{𝟚}} itself. They construct the infinite real
projective space $\mathbf{RP}^∞$ by using universal covering spaces,
and show that it is homotopy equivalent to the Eilenberg-Maclane space
$K(\mathbb{Z}/2\mathbb{Z},1)$ which classifies all the 0-sphere
bundles. Our reversible programming language is exactly the syntactic
presentation of this classifying space. If we choose
{\small\AgdaDatatype{𝕊¹}} instead of {\small\AgdaDatatype{𝕊⁰}}, we get
the infinite complex projective space $\mathbf{CP}^∞$, but it remains
to investigate what kind of reversible programming language this would
lead to.

If we consider the $\Pi$ language over all finite types, we conjecture
that we should get a representation of
$\coprod_{n\in\mathbb{N}}K(S_n,1)$ where $S_n$ is the symmetric
group. The idea is that the $n^\mathrm{th}$ homotopy group of an
Eilenberg-Maclane space $K(G,n)$ is isomorphic to $G$ (and every other
homotopy group is trivial). Thus, all necessary information about
paths and equivalences between finite types is captured in this model.

% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% \section{Conclusion}
% \label{sec:conclusion}

% What is $\bracket{S^1}$?  Is it useful for programming?  What about $\bracket{\mathbb{N}}$?

% What is the ``right'' generalization of $\bracket{-}$ so that we may have all
% the usual finite types (such as the ones available in $\Pi$) properly
% represented?

% \jacques{It is not clear to me that just taking a disjoint union over all the
%   types gives the correct generalization.}

% Looking at this from the other end: given some ``exotic'' (but finitely
% presented) Groupoid $\mathfrak{G}$, is there always a programming language
% which is sound and complete for $\mathfrak{G}$ ?

\ack We would like to thank Robert Rose for developing the model based
on univalent fibrations, for extensive contributions to the code, and for
numerous discussions.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\bibliographystyle{acm}
{
  \footnotesize
  \bibliography{cites}
}

\end{document}
