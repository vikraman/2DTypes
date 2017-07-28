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

\usepackage[conor,references]{agda}
\usepackage[mathscr]{euscript}
\usepackage[euler]{textgreek}
\usepackage{mathabx}
\usepackage{isomath}

\DeclareUnicodeCharacter {120794}{$\mathbb {2}$}
\DeclareUnicodeCharacter {9726}{$\sqbullet$}
\DeclareUnicodeCharacter {120792}{$\mathbb {0}$}
\DeclareUnicodeCharacter {119932}{$\mathbfit{U}$}

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
\newcommand{\PiTwo}{\ensuremath{\Pi_{\mathbb{2}}}}

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
transport P (refl x) = id

PathOver : {A : 𝒰} (P : A → 𝒰) {x y : A} (p : x == y) (u : P x) (v : P y) → 𝒰
PathOver P p u v = transport P p u == v

syntax PathOver P p u v = u == v [ P ↓ p ]

apd : {A : 𝒰} {P : A → 𝒰} {x y : A} (f : (a : A) → P a) (p : x == y) → f x == f y [ P ↓ p ]
apd f (refl x) = refl (f x)
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
reversible languages on one hand and univalent universes on the other. In the
next section, we give a rational reconstruction of $\Pi$ focusing on a small
``featherweight'' fragment. In Sec.~\ref{sec:univalent}, we review
\emph{univalent fibrations} which allow us to give formal presentations of
``small'' univalent universes. In Sec.~\ref{sec:correspondence} we state and prove
the formal connection between the systems presented in the preceding two
sections.  Sec.~\ref{sec:discussion} discusses the implications of our work
and situates it into the broader context of the existing literature.
%% Sec.~\ref{sec:conclusion} right now is a stub, and may not
%% survive?

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{A Simple Reversible Programming Languages}

Starting from the physical principle of ``conservation of
information''~\cite{Hey:1999:FCE:304763,fredkin1982conservative}, James and
Sabry~\cite{James:2012:IE:2103656.2103667} propose a family of programming
languages $\Pi$ in which computation preserve information. Technically,
computations are \emph{type isomorphisms} which, at least in the case of finite
types, clearly preserve entropy in the information-theoretic
sense~\cite{James:2012:IE:2103656.2103667}. We illustrate the general flavor of
the family of languages with some examples and then identify a ``featherweight''
version of $\Pi$ to use in our formal development.

%%%%%
\subsection{Examples}

The examples below assume a representation of the type of booleans $\bt$ as the
disjoint union $\ot \oplus \ot$ with the left injection representing
$\mathsf{false}$ and the right injection representing $\mathsf{true}$. Given an
arbitrary reversible function $\AgdaFunction{f}$ of type $a \leftrightarrow a$,
we can build the reversible function
$\AgdaFunction{controlled}~\AgdaFunction{f}$ that takes a pair of type
$\bt \otimes a$ and checks the incoming boolean; if it is false (i.e., we are in
the left injection), the function behaves like the identity; otherwise the
function applies $\AgdaFunction{f}$ to the second argument. The incoming boolean
is then reconstituted to maintain reversibility:

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

\noindent The left column shows the sequence of types that are visited during
the computation; the right column shows the names of the combinators\footnote{We
  use names that are hopefully quite mnemonic; for the precise definitions of
  the combinators see the $\Pi$-papers.} that witness the corresponding type
isomorphism. The code for $\AgdaFunction{controlled}~\AgdaFunction{f}$ provides
constructive evidence (i.e., a program, a logic gate, or a hardware circuit) for
an automorphism on $\bt \otimes a$: it can be read top-down or bottom-up to go
back and forth.

The $\AgdaFunction{not}$ function below is a simple lifting of
\AgdaFunction{swap₊} which swaps the left and right injections in a sum
type. Using the \AgdaFunction{controlled} building block, we can build a
controlled-not ($\AgdaFunction{cnot}$) gate and a controlled-controlled-not
gate, also known as the \AgdaFunction{toffoli} gate. The latter gate is a
universal function for combinational boolean circuits thus showing the
expressiveness of the language:

{\small
\[\begin{array}{rcl}
\AgdaFunction{not} &:& \bt \iso \bt \\
\AgdaFunction{not} &=&
  \AgdaFunction{unfoldBool} \odot \AgdaFunction{swap₊} \odot \AgdaFunction{foldBool} \\
\\
\AgdaFunction{cnot} &:& \bt \otimes \bt \iso \bt \otimes \bt \\
\AgdaFunction{cnot} &=& \AgdaFunction{controlled}~\AgdaFunction{not} \\
\\
\AgdaFunction{toffoli} &:& \bt \otimes (\bt \otimes \bt)
                           \iso \bt \otimes (\bt \otimes \bt) \\
\AgdaFunction{toffoli} &=& \AgdaFunction{controlled}~\AgdaFunction{cnot} \\
\end{array}\]}
%%%

\noindent While we wrote \AgdaFunction{controlled} in equational-reasoning
style, \AgdaFunction{not} is written in the point-free combinator style.  These
are equivalent as $\byiso{-}$ is defined in terms of the sequential composition
combinator $\odot$.

As is customary in any semantic perspective on programming languages, we are
interested in the question of when two programs are ``equivalent.'' Consider the
following six programs of type~$\bt \iso \bt$:

{\small
\[\def\arraystretch{1.2}\begin{array}{rcl}
\AgdaFunction{id₁}~\AgdaFunction{id₂}~\AgdaFunction{id₃}~
  \AgdaFunction{not₁}~\AgdaFunction{not₂}~\AgdaFunction{not₃} &:& \bt \iso \bt \\
\AgdaFunction{id₁} &=&
  \AgdaFunction{id} \odot \AgdaFunction{id} \\
\AgdaFunction{id₂} &=&
  \AgdaFunction{not} \odot \AgdaFunction{id} \odot \AgdaFunction{not} \\
\AgdaFunction{id₃} &=&
  \AgdaFunction{uniti⋆} \odot \AgdaFunction{swap⋆} \odot
                        (\AgdaFunction{id} \otimes \AgdaFunction{id}) \odot
                        \AgdaFunction{swap⋆} \odot
                        \AgdaFunction{unite⋆} \\
\AgdaFunction{not₁} &=&
  \AgdaFunction{id} \odot \AgdaFunction{not} \\
\AgdaFunction{not₂} &=&
  \AgdaFunction{not} \odot \AgdaFunction{not} \odot \AgdaFunction{not} \\
\AgdaFunction{not₃} &=&
  \AgdaFunction{uniti⋆} \odot \AgdaFunction{swap⋆} \odot
                        (\AgdaFunction{not} \otimes \AgdaFunction{id}) \odot
                        \AgdaFunction{swap⋆} \odot
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
\caption{\label{fig:not}Graphical representation of \AgdaFunction{not₃}}
\end{figure}

\noindent The programs are all of the same type but this is clearly not a
sufficient condition for ``equivalence.'' Thinking extensionally, i.e., by
looking at all possible input-output pairs, it is easy to verify that the six
programs split into two classes: one equivalent to the identity function and one
equivalent to the boolean negation. In the context of $\Pi$, we can better: we
can provide \emph{evidence} (i.e., a program that manipulates programs) that can
constructively transform every program to an equivalent one. We show such a
level-2 program proving that $\AgdaFunction{not₃}$ is equivalent to
$\AgdaFunction{not}$. For illustration, the program for $\AgdaFunction{not₃}$ is
depicted in Fig.~\ref{fig:not}. We encourage the reader to map the steps below
to manipulations on the diagram that would incrementally simplify it:

{\small
\[\def\arraystretch{1.2}\begin{array}{rcll}
\AgdaFunction{notOpt} &:& \AgdaFunction{not₃} \isotwo \AgdaFunction{not} \\
\AgdaFunction{notOpt} &=&
  \AgdaFunction{uniti⋆} \odot (\AgdaFunction{swap⋆} \odot
                        ((\AgdaFunction{not} \otimes \AgdaFunction{id}) \odot
                        (\AgdaFunction{swap⋆} \odot \AgdaFunction{unite⋆})))
 & \quad\byisotwo{\AgdaFunction{id} \boxdot \AgdaFunction{assocLeft}} \\
&& \AgdaFunction{uniti⋆} \odot (\AgdaFunction{swap⋆} \odot
                        (\AgdaFunction{not} \otimes \AgdaFunction{id})) \odot
                        (\AgdaFunction{swap⋆} \odot \AgdaFunction{unite⋆})
 & \quad\byisotwo{\AgdaFunction{id} \boxdot (\AgdaFunction{swapLeft}
                                  \boxdot \AgdaFunction{id})} \\
&& \AgdaFunction{uniti⋆} \odot ((\AgdaFunction{id} \otimes \AgdaFunction{not})
                      \odot \AgdaFunction{swap⋆}) \odot
                        (\AgdaFunction{swap⋆} \odot \AgdaFunction{unite⋆})
 & \quad\byisotwo{\AgdaFunction{id} \boxdot \AgdaFunction{assocRight}} \\
&& \AgdaFunction{uniti⋆} \odot ((\AgdaFunction{id} \otimes \AgdaFunction{not})
                      \odot (\AgdaFunction{swap⋆} \odot
                        (\AgdaFunction{swap⋆} \odot \AgdaFunction{unite⋆})))
 & \quad\byisotwo{\AgdaFunction{id} \boxdot (\AgdaFunction{id}
                                  \boxdot \AgdaFunction{assocLeft})} \\
&& \AgdaFunction{uniti⋆} \odot ((\AgdaFunction{id} \otimes \AgdaFunction{not})
                      \odot ((\AgdaFunction{swap⋆} \odot
                      \AgdaFunction{swap⋆}) \odot \AgdaFunction{unite⋆}))
 & \quad\byisotwo{\AgdaFunction{id} \boxdot (\AgdaFunction{id}
                                  \boxdot (\AgdaFunction{leftInv} \boxdot \AgdaFunction{id}))} \\
&& \AgdaFunction{uniti⋆} \odot ((\AgdaFunction{id} \otimes \AgdaFunction{not})
                      \odot (\AgdaFunction{id} \odot \AgdaFunction{unite⋆}))
 & \quad\byisotwo{\AgdaFunction{id} \boxdot (\AgdaFunction{id}
                                  \boxdot \AgdaFunction{idLeft})} \\
&& \AgdaFunction{uniti⋆} \odot ((\AgdaFunction{id} \otimes \AgdaFunction{not})
                      \odot \AgdaFunction{unite⋆})
 & \quad\byisotwo{\AgdaFunction{assocLeft}} \\
&& (\AgdaFunction{uniti⋆} \odot (\AgdaFunction{id} \otimes \AgdaFunction{not}))
                      \odot \AgdaFunction{unite⋆}
 & \quad\byisotwo{\AgdaFunction{unitiLeft} \boxdot \AgdaFunction{id}} \\
&& (\AgdaFunction{not} \otimes \AgdaFunction{uniti⋆}) \odot \AgdaFunction{unite⋆}
 & \quad\byisotwo{\AgdaFunction{assocRight}} \\
&& \AgdaFunction{not} \otimes (\AgdaFunction{uniti⋆} \odot \AgdaFunction{unite⋆})
 & \quad\byisotwo{\AgdaFunction{id} \boxdot \AgdaFunction{leftInv}} \\
&& \AgdaFunction{not} \otimes \AgdaFunction{id}
 & \quad\byisotwo{\AgdaFunction{idRight}} \\
&& \AgdaFunction{not}
\end{array}\]}

\noindent It is worthwhile mentioning that the above derivation could also be
drawn as one (large!) commutative diagram in an appropriate category, with each
$\byisotwo{-}$ as a $2$-arrow (and representing a natural isomorphism).  See
Shulman's draft book~\cite{shulman} for that interpretation.

%%%%%
\subsection{\PiTwo}{\label{sec:pi2}}

Having illustrated the general flavor of the $\Pi$ family of
languages, we present in full detail a small $\Pi$-based language
which we will use in the formalization in the rest of the paper. The
language is the restriction of $\Pi$ to the case of just one
type $\mathbb{2}$
{
\begin{code}
data 𝟚 : 𝒰 where 0₂ 1₂ : 𝟚
\end{code}
}
The syntax of \PiTwo is given below:

%% \[\def\arraystretch{0.8}\begin{array}{l@{\quad}rclrl}
%% (\textit{Types}) & \tau &::=& \bt \\
%% \\
%% (\textit{Terms}) &  v &::=& \fc &:& \bt \\
%%               && \alt & \tc &:& \bt \\
%% \\
%%  (\textit{1-combinators}) &  c &::=& \id &:& \tau \iso \tau \\
%%                && \alt & \swap &:& \bt \iso \bt \\
%%                && \alt & ! &:& (\tau_1 \iso \tau_2) \to (\tau_2 \iso \tau_1) \\
%%                && \alt & \odot &:& (\tau_1 \iso \tau_2) \to (\tau_2 \iso \tau_3) \to (\tau_1 \iso \tau_3)  \\
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

\AgdaHide{
\begin{code}
infix 3 _↔₁_ _↔₂_ _↔₃_
infix 5 !₁_ !₂_
infix 4 _⊙₁_ _⊙₂_
\end{code}
}

{
\begin{code}
data 𝑼 : 𝒰 where `𝟚 : 𝑼

data _↔₁_ : 𝑼 → 𝑼 → 𝒰 where
  `id  : {A : 𝑼} → A ↔₁ A
  `not : `𝟚 ↔₁ `𝟚
  !₁_  : {A B : 𝑼} → A ↔₁ B → (B ↔₁ A)
  _⊙₁_ : {A B C : 𝑼} → (A ↔₁ B) → (B ↔₁ C) → (A ↔₁ C)

data _↔₂_ : {A B : 𝑼} → (A ↔₁ B) → (A ↔₁ B) → 𝒰 where
  `id₂   : {A B : 𝑼} {p : A ↔₁ B} → p ↔₂ p
  `idl   : {A B : 𝑼} (p : A ↔₁ B) → `id ⊙₁ p ↔₂ p
  `idr   : {A B : 𝑼} (p : A ↔₁ B) → p ⊙₁ `id ↔₂ p
  `!l    : {A B : 𝑼} (p : A ↔₁ B) → p ⊙₁ !₁ p ↔₂ `id
  `!r    : {A B : 𝑼} (p : B ↔₁ A) → !₁ p ⊙₁ p ↔₂ `id
  `!id   : {A : 𝑼} → !₁ `id {A} ↔₂ `id {A}
  `!not  : !₁ `not ↔₂ `not
  `!◾    : {A B C : 𝑼} {p : A ↔₁ B} {q : B ↔₁ C} → !₁ (p ⊙₁ q) ↔₂ (!₁ q) ⊙₁ (!₁ p)
  `!!    : {A B : 𝑼} {p : A ↔₁ B} → !₁ (!₁ p) ↔₂ p
  `assoc : {A B C D : 𝑼} (p : A ↔₁ B) (q : B ↔₁ C) (r : C ↔₁ D)
         → (p ⊙₁ q) ⊙₁ r ↔₂ p ⊙₁ (q ⊙₁ r)
  `!     : {A B : 𝑼} {p q : A ↔₁ B} → p ↔₂ q → !₁ p ↔₂ !₁ q
  !₂_      : {A B : 𝑼} {p q : A ↔₁ B} → (u : p ↔₂ q) → q ↔₂ p
  _⊙₂_   : {A B : 𝑼} {p q r : A ↔₁ B} → (u : p ↔₂ q) (v : q ↔₂ r) → (p ↔₂ r)
  _□₂_   : {A B C : 𝑼} {p q : A ↔₁ B} {r s : B ↔₁ C}
         → (u : p ↔₂ q) (v : r ↔₂ s) → (p ⊙₁ r) ↔₂ (q ⊙₁ s)

data _↔₃_ {A B : 𝑼} {p q : A ↔₁ B} (u v : p ↔₂ q) : 𝒰 where
  `trunc : u ↔₃ v
\end{code}
}
\jacques{The text below doesn't make sense anymore as the
``syntactic categories'' were named in the above
commented out array, but have different names in the Agda
code.}

The syntactic category $c$ is that of 1-combinators denoting
reversible programs, type isomorphisms, permutations, or equivalences
depending on one's favorite interpretation. There are two primitive
combinators $\id$ and $\swap$ which are closed under inverses $!$ and
sequential composition $\odot$. The syntactic category $\alpha$ is
that of 2-combinators denoting reversible program transformations,
coherence conditions on type isomorphisms, equivalences between
permutations, or program optimizations depending on one's favorite
interpretation.

It is relatively easy to think of a few sound program transformations to include
in the category $\alpha$ of 2-combinators. But, as the following lemma
establishes, the above set is \emph{complete}:

\begin{lemma}[Canonical Forms]
  Given a 1-combinator $c : \tau \iso \tau$, we either have a
  2-combinator of type $c \isotwo \AgdaFunction{`id}$ or a 2-combinator of type
  $c \isotwo \AgdaFunction{`not}$. In other words, every 1-combinator has a canonical
  representation as either $\AgdaFunction{`id}$ or $\AgdaFunction{`not}$ and the set of 2-combinators is rich
  enough to normalize $c$ to its canonical representation.
\end{lemma}

\noindent For example, composition of negation is equivalent to the identity:
{
\begin{code}
not⊙₁not↔₂id : `not ⊙₁ `not ↔₂ `id
not⊙₁not↔₂id = ((!₂ `!not) □₂ `id₂) ⊙₂ (`!r `not)
\end{code}
}

To achieve this, we need a type which encodes exactly this
knowledge: \AgdaDatatype{Which} names the subset of
\AgdaDatatype{↔₁} which are canonical forms.
{
\begin{code}
data Which : 𝒰 where ID NOT : Which

refine : (w : Which) → `𝟚 ↔₁ `𝟚
refine ID = `id
refine NOT = `not
\end{code}
}

This in turn enables us to compute for any
2-combinator $c$ (the name of) its canonical form, as
well as a proof that $c$ is equivalent to its
canonical form.
{
\begin{code}
canonical : (c : `𝟚 ↔₁ `𝟚) → Σ[ c' ∶ Which ] (c ↔₂ (refine c'))
canonical `id = ID , `id₂
canonical `not = NOT , `id₂
canonical (!₁ c) with canonical c
... | ID , c↔₂id = ID , (`! c↔₂id ⊙₂ `!id)
... | NOT , c↔₂not = NOT , (`! c↔₂not ⊙₂ `!not)
canonical (_⊙₁_ {_} {`𝟚} c₁ c₂) with canonical c₁ | canonical c₂
... | ID , c₁↔₂id | ID , c₂↔₂id = ID , ((c₁↔₂id □₂ c₂↔₂id) ⊙₂ `idl `id)
... | ID , c₁↔₂id | NOT , c₂↔₂not = NOT , ((c₁↔₂id □₂ c₂↔₂not) ⊙₂ `idl `not)
... | NOT , c₁↔₂not | ID , c₂↔₂id = NOT , ((c₁↔₂not □₂ c₂↔₂id) ⊙₂ `idr `not)
... | NOT , c₁↔₂not | NOT , c₂↔₂not = ID , ((c₁↔₂not □₂ c₂↔₂not) ⊙₂ not⊙₁not↔₂id)
\end{code}
}
It is worthwhile to note that the proof of \AgdaSymbol{canonical} does
not use all the level 2 combinators.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Univalent Fibrations}
\label{sec:univalent}

We work in intensional type theory with one univalent universe \AgdaSymbol{𝒰}
closed under propositional truncation.  The rest of this section is
devoted to explaining what that means.  We follow the terminology used
in~\cite{hottbook}.  For brevity, we will often given just signatures and
elide the body\footnote{The full code can be found in our github
repository; for this section, our work is essentially isomorphic to
the HoTT Agda library, also on github.}.

\subsection{Equivalences}

Given types \AgdaSymbol{A} and \AgdaSymbol{B}, a function
\AgdaSymbol{f : A → B} is a quasi-inverse, if there is another
function \AgdaSymbol{g : B → A} which acts as both a left and
right inverse to \AgdaSymbol{f}.
%
\begin{code}
is-qinv : {A B : 𝒰} → (f : A → B) → 𝒰
is-qinv {A} {B} f = Σ[ g ∶ (B → A) ] (g ∘ f ∼ id × f ∘ g ∼ id)
\end{code}
%
To make this type contractible, we need to
%
\begin{code}
is-hae : {A B : 𝒰} → (f : A → B) → 𝒰
is-hae {A} {B} f = Σ[ g ∶ (B → A) ] Σ[ η ∶ g ∘ f ∼ id ]
                   Σ[ ε ∶ f ∘ g ∼ id ] (ap f ∘ η ∼ ε ∘ f)

qinv-is-hae : {A B : 𝒰} {f : A → B} → is-qinv f → is-hae f
\end{code}
\AgdaHide{
\begin{code}
qinv-is-hae = {!!}
\end{code}
}
%
Then we can define a type of equivalences between two types.
%
\begin{code}
_≃_ : (A B : 𝒰) → 𝒰
A ≃ B = Σ[ f ∶ (A → B) ] is-hae f
\end{code}

\subsection{Type Families are Fibrations}

A type family \AgdaSymbol{P} over a type \AgdaSymbol{A} is a fibration with base
space \AgdaSymbol{A}, and \AgdaSymbol{P x} the fiber over \AgdaSymbol{x}. The
total space is given by \AgdaSymbol{Σ[ x ∶ A ] P x}. The path lifting property
can be defined by path induction.

\begin{code}
lift : {A : 𝒰} {P : A → 𝒰} {x y : A}
     → (u : P x) (p : x == y)
     → (x , u) == (y , transport P p u)
lift u (refl x) = refl (x , u)
\end{code}
%
Because the pattern \AgdaSymbol{transport P p u == v} recurs often, we define
the syntax \AgdaSymbol{u == v [ P ↓ p ]} as a synonym for it, which indicates
the path in the fiber \AgdaSymbol{P} over \AgdaSymbol{u} and \AgdaSymbol{v},
which lies over \AgdaSymbol{p}. This is essentially the \AgdaSymbol{PathOver}
type pioneered by Licata and Brunerie in \cite{licata2015cubical}. It is
important to note the ``flip'' in the syntax. Such paths in the total space
induce other paths:

\begin{code}
module _ {A : 𝒰} {P : A → 𝒰} {a b : A} {pa : P a} {pb : P b} where
  dpair= : Σ[ p ∶ a == b ] (pa == pb [ P ↓ p ])
         → (a , pa) == (b , pb)
  dpair= (refl a , refl pa) = refl (a , pa)

  dpair=-β₁ : (w : Σ[ p ∶ a == b ] (pa == pb [ P ↓ p ]))
            → (ap pr₁ ∘ dpair=) w == pr₁ w
  dpair=-β₁ (refl a , refl pa) = refl (refl a)

  dpair=-e₁ : (a , pa) == (b , pb) → a == b
  dpair=-e₁ = ap pr₁
\end{code}

\subsection{Paths to Equivalences}

The \AgdaSymbol{transport} operation lifts paths to equivalences. By
transporting identity, we can convert a path to an equivalence.

\jacques{But transport does not occur below at all, not even
implicitly.  In fact, the 4 functions below are so trivial that
they could be collapsed into 1 without loss of comprehension.
Compared to how complex a lot of the rest of this is (such as
the previous sub-section), what's the point of taking so much
space with this?}

\begin{code}
idh : {A : 𝒰} {P : A → 𝒰} → (f : Π[ a ∶ A ] P a) → f ∼ f
idh f a = refl (f a)

ide : (A : 𝒰) → A ≃ A
ide A = id , id , idh id , idh id , idh (idh id)

tpt-eqv : {A : 𝒰} (P : A → 𝒰) → {a b : A} → a == b → P a ≃ P b
tpt-eqv P (refl a) = ide (P a)

id-to-eqv : {A B : 𝒰} → A == B → A ≃ B
id-to-eqv = tpt-eqv id
\end{code}

\subsection{Univalent Fibrations}

A type family (fibration) \AgdaSymbol{P : A → 𝒰} is univalent if the map
\AgdaSymbol{tpt-eqv p} is an equivalence, that is, paths in the base space are
\emph{equivalent} to equivalences in the fiber. In general, univalent fibrations
are defined by Kapulkin and Lumsdaine~\cite{SimplicialModel} in the simplicial
set model (SSet).

\begin{code}
is-univ-fib : {A : 𝒰} (P : A → 𝒰) → 𝒰
is-univ-fib {A} P = ∀ (a b : A) → is-hae (tpt-eqv P {a} {b})
\end{code}
%
The univalence axiom (for \AgdaSymbol{𝒰}) is a specialization
of \AgdaSymbol{is-univ-fib} to the identity fibration.  We
postulate this as an axiom.  We also give a short-form
\AgdaSymbol{ua} for getting a path from an equivalence.
%
\begin{code}
module _ {A B : 𝒰} where
  postulate
    univalence : is-hae (id-to-eqv {A} {B})

  ua : A ≃ B → A == B
  ua = pr₁ univalence
\end{code}

\AgdaHide{
\begin{code}
  ua-β : id-to-eqv ∘ ua ∼ id
  ua-β = pr₁ (pr₂ (pr₂ univalence))

  ua-β₁ : transport id ∘ ua ∼ pr₁
  ua-β₁ = {!!} -- dpair=-e₁ ∘ ua-β

  ua-η : ua ∘ id-to-eqv ∼ id
  ua-η = pr₁ (pr₂ univalence)

ua-ide : {A : 𝒰} → ua (ide A) == refl A
ua-ide {A} = ua-η (refl A)
\end{code}
}
%
We can define universes a l\`{a} Tarski by having a code \AgdaSymbol{U}
for the universe \AgdaSymbol{𝒰}, and an interpretation function \AgdaSymbol{El} into
\AgdaSymbol{𝒰}. This enables us to define a univalent universe as follows.

\begin{code}
Ũ = Σ[ U ∶ 𝒰 ] (U → 𝒰)

is-univalent : Ũ → 𝒰
is-univalent (U , El) = is-univ-fib El
\end{code}

\subsection{Propositional Truncation}

A type \AgdaSymbol{A} is \emph{contractible} (h-level 0, or (-2)-truncated), if
it has a center of contraction, and all other terms of that type are connected
to it by a path.

\begin{code}
is-contr : (A : 𝒰) → 𝒰
is-contr A = Σ[ a ∶ A ] Π[ b ∶ A ] (a == b)
\end{code}
%
Equivalences are contractible (assuming univalence):
\begin{code}
is-hae-is-contr : {A B : 𝒰} {f : A → B} → is-hae f → is-contr (is-hae f)
\end{code}
\AgdaHide{
\begin{code}
is-hae-is-contr = {!!}
\end{code}
}
%
A type \AgdaSymbol{A} is a \emph{proposition} (h-level 1, or (-1)-truncated) if
all pairs of terms of that type are connected by a path. Such a type can have at
most one inhabitant - in other words, it is ``contractible if inhabited''.  A
type \AgdaSymbol{A} is a \emph{set} if for any two terms $a, b$ of
\AgdaSymbol{A}, its type of paths \AgdaSymbol{a == b} is a proposition.

\begin{code}
is-prop : (A : 𝒰) → 𝒰
is-prop A = Π[ a ∶ A ] Π[ b ∶ A ] (a == b)

is-set : (A : 𝒰) → 𝒰
is-set A = Π[ a ∶ A ] Π[ b ∶ A ] is-prop (a == b)
\end{code}
%
\AgdaHide{
\begin{code}
prop-is-set : {A : 𝒰} → is-prop A → is-set A
prop-is-set φ a b p q = {!!}

is-hae-is-prop : {A B : 𝒰} {f : A → B} → is-prop (is-hae f)
is-hae-is-prop = {!!}

eqv= : {A B : 𝒰} {eqv eqv' : A ≃ B} → (pr₁ eqv == pr₁ eqv') → eqv == eqv'
eqv= φ = dpair= (φ , is-hae-is-prop _ _)
\end{code}
}
Any type can be truncated to a proposition by freely adding paths. This is the
propositional truncation (or (-1)-truncation) which can be expressed as a higher
inductive type (HIT). The type constructor \AgdaSymbol{∥\_∥} takes a type
\AgdaSymbol{A} as a parameter, and the point constructor \AgdaSymbol{∣\_∣}
coerces terms of type \AgdaSymbol{A} to terms in the truncation. The path
constructor \AgdaSymbol{ident} identifies any two points in the truncation,
making it a proposition.  We must do this as a \AgdaKeyword{postulate} as
Agda does not yet support HITs.

\begin{code}
postulate
    ∥_∥ : (A : 𝒰) → 𝒰
    ∣_∣ : {A : 𝒰} → (a : A) → ∥ A ∥
    ident : {A : 𝒰} {a b : ∥ A ∥} → a == b

∥-∥-is-prop : {A : 𝒰} → is-prop ∥ A ∥
∥-∥-is-prop _ _ = ident
\end{code}
%
This makes \AgdaSymbol{∥ A ∥} the ``free'' proposition on any type
\AgdaSymbol{A}. It can be viewed as the left adjoint to the forgetful functor
from propositions to types. The recursion principle (below) ensures that we can
only eliminate a propositional truncation to a type that is a proposition.

\begin{code}
module _ {A : 𝒰} (P : 𝒰) (f : A → P) (_ : is-prop P) where
  postulate
    rec-∥-∥ : ∥ A ∥ → P
    rec-∥-∥-β : Π[ a ∶ A ] (rec-∥-∥ ∣ a ∣ == f a)
\end{code}

\subsection{Singleton subuniverses}

Given any type \AgdaSymbol{T}, we can build a propositional predicate that only
picks out \AgdaSymbol{T}. This lets us build up a singleton ``subuniverse'' of
\AgdaSymbol{𝒰}, which is only inhabited by \AgdaSymbol{T}.  We will eventually
show that all such sub-universes are univalent.

\begin{code}
is-type : (T : 𝒰) → 𝒰 → 𝒰
is-type T = λ X → ∥ X == T ∥

Ũ[_] : (T : 𝒰) → Ũ
Ũ[ T ] = Σ 𝒰 (is-type T) , λ _ → T
\end{code}

The following lemma by Christensen gives a characterization of univalent
fibrations for singleton subuniverses. If \AgdaSymbol{T : 𝒰} is a type, then
\AgdaSymbol{pr₁ : Ũ[ T ] → 𝒰} is a univalent fibration, with base
\AgdaSymbol{(T, ∣ refl T ∣)}.

\jacques{Calling it pr₁, while technically correct, makes things hard to
understand.  It's not ``first projection'' which is a univalent fibration,
but rather ``code-of'' (or even ``code'').  Can we rename this?}

Towards proving that, we start by defining the automorphism group of a space in
an $(∞, 1)$-topos. By working in the internal language, that is, in HoTT, we can
define the type \AgdaSymbol{Aut T} for any type \AgdaSymbol{T : 𝒰} to be the
type of automorphisms on \AgdaSymbol{T} which gives rise to an
$∞$-group. Similarly, the delooping of this group is the type of connected
components of \AgdaSymbol{T}, which is suggestively named \AgdaSymbol{BAut
T}. The loopspace of any pointed type \AgdaSymbol{(T , t)} is the space of paths
on \AgdaSymbol{t}, \AgdaSymbol{Ω (T , t)}.

\begin{code}
Aut : (T : 𝒰) → 𝒰
Aut T = T ≃ T

BAut : (T : 𝒰) → 𝒰
BAut T = Σ[ X ∶ 𝒰 ] ∥ X ≃ T ∥

b₀ : {T : 𝒰} → BAut T
b₀ {T} = T , ∣ ide T ∣

Ω : Σ[ T ∶ 𝒰 ] T → 𝒰
Ω (T , t) = t == t

tpt-eqv-pr₁ : {T : 𝒰} {v w : BAut T} (p : v == w)
            → pr₁ (tpt-eqv pr₁ p) == transport id (dpair=-e₁ p)
tpt-eqv-pr₁ (refl v) = refl id
\end{code}

Putting these ingredients together, we can show that the
code of a singleton universe \AgdaSymbol{Ũ[ T ]} is a
univalent fibration.

\begin{code}
is-univ-fib-pr₁ : {T : 𝒰} → is-univ-fib pr₁
is-univ-fib-pr₁ (T , q) (T' , q') = qinv-is-hae (g , η , ε)
  where g : T ≃ T' → T , q == T' , q'
        g eqv = dpair= (ua eqv , ident)
        η : g ∘ tpt-eqv pr₁ ∼ id
        η (refl ._) = ap dpair= ( dpair= (ua-ide
                                  , prop-is-set (λ _ _ → ident) _ _ _ _))
        ε : tpt-eqv pr₁ ∘ g ∼ id
        ε eqv = eqv= ( tpt-eqv-pr₁ (dpair= (ua eqv , ident))
                     ◾ ap (transport id) (dpair=-β₁ (ua eqv , ident))
                     ◾ ua-β₁ eqv )
\end{code}

As a consequence, we have that the loopspace of the delooping the group
of automorphisms of a type \AgdaSymbol{T} is equivalent to the
type \AgdaSymbol{Aut(T)}.
%
% \AgdaSymbol{Ω(BAut(T)) ≃ Aut(T)} for any type \AgdaSymbol{T : 𝒰}.

\begin{code}
ΩBAut≃Aut[_] : (T : 𝒰) → Ω (BAut T , b₀) ≃ Aut T
ΩBAut≃Aut[ T ] = tpt-eqv pr₁ , is-univ-fib-pr₁ b₀ b₀
\end{code}

It remains to check that \AgdaSymbol{BAut T} is the same as our
singleton universe \AgdaSymbol{Ũ[ T ]}. This follows by univalence and
the universal property of truncation.

\AgdaHide{
% Only show this if you will provide the proof - otherwise the
% statement is already in the paragraph above.
\begin{code}
BAut≃Ũ[_] : (T : 𝒰) → BAut T ≃ pr₁ Ũ[ T ]
BAut≃Ũ[ T ] = {!!}
\end{code}
}
\subsection{The subuniverse {\normalfont\AgdaSymbol{U[𝟚]}}}
\jacques{I find it confusing that this has no tilde on the U}.

We define a particular subuniverse \AgdaSymbol{U[𝟚]} that we use in the
next section.
% \AgdaSymbol{𝟚} is the \AgdaSymbol{Bool} datatype, which is
% a set with two distinct points \AgdaSymbol{0₂} and \AgdaSymbol{1₂}.

\begin{code}
U[𝟚] = pr₁ Ũ[ 𝟚 ]
\end{code}

Instantiating the lemma from the previous section with \AgdaSymbol{𝟚}, we have
that \AgdaSymbol{U[𝟚]} is a univalent subuniverse, with \AgdaSymbol{pr₁} the
univalent fibration. By the property of being a univalent fibration we have
that \AgdaSymbol{Ω(BAut(𝟚) , 𝟚₀) ≃ (𝟚 ≃ 𝟚)}, where
\begin{code}
𝟚₀ = (𝟚 , ∣ ide 𝟚 ∣)
\end{code}
Since \AgdaSymbol{(𝟚 ≃ 𝟚) ≃ 𝟚} (see~\cite{hottbook} exercise 2.13), we have
\AgdaHide{\begin{code}
postulate
\end{code}}
\begin{code}
  𝟚≃Ω𝟚₀ : 𝟚 ≃ (𝟚₀ == 𝟚₀)
\end{code}
Therefore we know that there are only two distinct 1-path. Calling them
\AgdaHide{\begin{code}
postulate
\end{code}}
\begin{code}
  id𝟚 not𝟚 : 𝟚₀ == 𝟚₀
\end{code}
we have this decomposition
\AgdaHide{\begin{code}
postulate
\end{code}}
\begin{code}
  all-1-path : (p : 𝟚₀ == 𝟚₀) → (p == id𝟚) + (p == not𝟚)
\end{code}
For 2-path, \AgdaSymbol{𝟚} is a set, with witness
\AgdaHide{\begin{code}
postulate
\end{code}}
\begin{code}
  𝟚is-set : is-set 𝟚
\end{code}
From this, tt is easy to obtain that \AgdaSymbol{𝟚₀ == 𝟚₀} is a set
and that 2-paths are contractible.
\begin{code}
Ω𝟚₀is-set : is-set (𝟚₀ == 𝟚₀)
Ω𝟚₀is-set = transport is-set (ua 𝟚≃Ω𝟚₀) 𝟚is-set
all-2-path : {p : 𝟚₀ == 𝟚₀} → (γ : p == p) → γ == refl p
all-2-path {p} γ = Ω𝟚₀is-set p p γ (refl p)
\end{code}

In next section, we will use \AgdaSymbol{all-1-path}
and \AgdaSymbol{all-2-path}
to show the correspondence between \AgdaSymbol{Ω(BAut(𝟚) , 𝟚₀)} and \PiTwo.
%% With a syntactic presentation of \AgdaSymbol{Ω(BAut(𝟚))},
%% we get all the automorphisms on \AgdaSymbol{𝟚}, which gives a complete model for
%% \PiTwo.

%% However, the problem is easier for \AgdaSymbol{𝟚}, because
%% \AgdaSymbol{Aut(𝟚) ≃ 𝟚}, which gives the following easy lemmas for
%% 1-paths and 2-paths on \AgdaSymbol{𝟚}: \AgdaSymbol{all-1-paths} and
%% \AgdaSymbol{all-2-paths}.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Correspondence}
\label{sec:correspondence}

In previous work, on $\Pi$ we noted a possible connection with HoTT:
\begin{quote}
  It is, therefore, at least plausible that a variant of HoTT based exclusively
  on reversible functions that directly correspond to equivalences would have
  better computational properties. Our current result is a step, albeit
  preliminary, in that direction as it only applies to finite
  types~\cite{Carette2016}.
\end{quote}
Formalizing, in a precise sense, the connection between reversible programs
based on combinators and paths in HoTT, as intuitive as it may seem, is however
difficult. Paths in HoTT come equipped with principles like the
``contractibility of singletons'', ``transport'', and ``path induction.'' None
of these principles seems to have any direct counterpart in the world of
reversible programming.

\AgdaHide{
\begin{code}
postulate
  lem : {p q r : Ω (BAut 𝟚 , b₀)} (p=r : p == r) (q=r : q == r) (u : p == q)
      → u == p=r ◾ ((! p=r) ◾ u ◾ q=r) ◾ (! q=r)
-- lem p=r q=r u = (! (◾unitr u))
--               ◾ ap (λ x → u ◾ x) (! (◾invr q=r))
--               ◾ ! (◾unitl (u ◾ q=r ◾ ! q=r))
--               ◾ ap (λ x → x ◾ u ◾ q=r ◾ ! q=r) (! (◾invr p=r))
--               ◾ ◾assoc _ _ _
--               ◾ ap (λ x → p=r ◾ x) (! (◾assoc _ _ _))
--               ◾ ap (λ x → p=r ◾ x) (! (◾assoc _ _ _))
--               ◾ ap (λ x → p=r ◾ x ◾ ! q=r) (◾assoc _ _ _)
\end{code}
}
At level $0$, the correspondence is straightforward, as both
\AgdaSymbol{𝑼} and \AgdaSymbol{BAut 𝟚} are singletons.
\begin{code}
⟦_⟧ : 𝑼 → BAut 𝟚
⟦ `𝟚 ⟧ = 𝟚₀

⟦_⟧⁻¹ : BAut 𝟚 → 𝑼
⟦ 𝟚₀ ⟧⁻¹ = `𝟚
\end{code}

Level $1$ is the first non-trivial level. To each syntactic combinator
$c$ of \AgdaSymbol{A ↔₁ B}, we can associate a path, and vice-versa.

\begin{code}
⟦_⟧₁ : {A B : 𝑼} → A ↔₁ B → ⟦ A ⟧ == ⟦ B ⟧
⟦_⟧₁⁻¹ : 𝟚₀ == 𝟚₀ → `𝟚 ↔₁ `𝟚
\end{code}

Canonical forms are key to $\AgdaSymbol{⟦\_⟧₁}$; \AgdaSymbol{all-1-path} is
key to $\AgdaSymbol{⟦\_⟧₁⁻¹}$.
\AgdaHide{
\begin{code}
⟦ p ⟧₁  = {!!}
⟦ p ⟧₁⁻¹ = {!!}
\end{code}
}

Level $2$ is tricky.  We know that all self-paths (through
\AgdaSymbol{all-2-paths}) are trivial.  In fact, all of them are.
Nevertheless $\AgdaSymbol{⟦\_⟧₂}$ requires quite a bit of work.
$\AgdaSymbol{⟦\_⟧₂⁻¹}$ proceeds by enumerating $1$-paths, which makes
things straightforward.
\begin{code}
⟦_⟧₂ : {A B : 𝑼} {p q : A ↔₁ B} → (u : p ↔₂ q) → ⟦ p ⟧₁ == ⟦ q ⟧₁
⟦_⟧₂⁻¹ : {p q : 𝟚₀ == 𝟚₀} → p == q → ⟦ p ⟧₁⁻¹ ↔₂ ⟦ q ⟧₁⁻¹
\end{code}

\AgdaHide{
\begin{code}
⟦ p ⟧₂ = {!!}
⟦ p ⟧₂⁻¹ = {!!}
\end{code}
}

Level $3$ is trivial -- by fiat.
\begin{code}
⟦_⟧₃ : {A B : 𝑼} {p q : A ↔₁ B} {u v : p ↔₂ q} → (α : u ↔₃ v) → ⟦ u ⟧₂ == ⟦ v ⟧₂
⟦_⟧₃⁻¹ : {p q : 𝟚₀ == 𝟚₀} {u v : p == q} → u == v → ⟦ u ⟧₂⁻¹ ↔₃ ⟦ v ⟧₂⁻¹
\end{code}

\begin{code}
⟦ `trunc ⟧₃ = refl _
⟦ _ ⟧₃⁻¹ = `trunc
\end{code}

Naturally, all of the preceding work would be much less interesting if
the correspondences were not coherent with each other.  First, they are
sound:
\begin{code}
⟦⟦_⟧₁⟧₁⁻¹ : (p : `𝟚 ↔₁ `𝟚) → p ↔₂ ⟦ ⟦ p ⟧₁ ⟧₁⁻¹
⟦⟦_⟧₁⁻¹⟧₁ : (p : 𝟚₀ == 𝟚₀) → p == ⟦ ⟦ p ⟧₁⁻¹ ⟧₁
\end{code}

But also complete.  Normally, completeness is a rather difficult result to
prove.  But in our case, all the infrastructure above means that these
are straightforward.  Key is \emph{reversibility}.  In the first proof
\AgdaSymbol{!₂} is essential, with \AgdaSymbol{!} being essential in
the second.
\begin{code}
completeness₁ : {p q : `𝟚 ↔₁ `𝟚} → ⟦ p ⟧₁ == ⟦ q ⟧₁ → p ↔₂ q
completeness₁ {p} {q} u = ⟦⟦ p ⟧₁⟧₁⁻¹ ⊙₂ (⟦ u ⟧₂⁻¹ ⊙₂ !₂ ⟦⟦ q ⟧₁⟧₁⁻¹)

completeness₁⁻¹ : {p q : 𝟚₀ == 𝟚₀} → ⟦ p ⟧₁⁻¹ ↔₂ ⟦ q ⟧₁⁻¹ → p == q
completeness₁⁻¹ {p} {q} u = ⟦⟦ p ⟧₁⁻¹⟧₁ ◾ ⟦ u ⟧₂ ◾ (! ⟦⟦ q ⟧₁⁻¹⟧₁)
\end{code}

Level $2$ soundness is trickier to state, mostly because the types involved in
$\AgdaSymbol{⟦ ⟦ u ⟧₂ ⟧₂⁻¹}$ and $\AgdaSymbol{⟦ ⟦ u ⟧₂⁻¹ ⟧₂}$ are non-trivial.  For
combinators, the result is trivial, again by fiat.  For paths, enumeration of
1-paths reduces the complexity of the problem to ``unwinding'' complex expressions
for identity paths.
\begin{code}
⟦⟦_⟧₂⟧₂⁻¹ : {p q : `𝟚 ↔₁ `𝟚} (u : p ↔₂ q) → u ↔₃ (⟦⟦ p ⟧₁⟧₁⁻¹ ⊙₂ (⟦ ⟦ u ⟧₂ ⟧₂⁻¹ ⊙₂ (!₂ ⟦⟦ q ⟧₁⟧₁⁻¹)))
⟦⟦_⟧₂⁻¹⟧₂ : {p q : 𝟚₀ == 𝟚₀} (u : p == q) → u == ⟦⟦ p ⟧₁⁻¹⟧₁ ◾ ⟦ ⟦ u ⟧₂⁻¹ ⟧₂ ◾ (! ⟦⟦ q ⟧₁⁻¹⟧₁)
\end{code}

Level $2$ completeness offers no new difficulties.
\begin{code}
completeness₂ : {p q : `𝟚 ↔₁ `𝟚} {u v : p ↔₂ q} → ⟦ u ⟧₂ == ⟦ v ⟧₂ → u ↔₃ v
completeness₂⁻¹ : {p q : 𝟚₀ == 𝟚₀} {u v : p == q} → ⟦ u ⟧₂⁻¹ ↔₃ ⟦ v ⟧₂⁻¹ → u == v
\end{code}

\AgdaHide{
\begin{code}
⟦⟦ p ⟧₁⟧₁⁻¹ = {!!}
⟦⟦ p ⟧₁⁻¹⟧₁ = {!!}

⟦⟦ u ⟧₂⟧₂⁻¹ = `trunc

⟦⟦_⟧₂⁻¹⟧₂ = {!!}

completeness₂ u = `trunc
completeness₂⁻¹ {p} {q} {u} {v} α = ⟦⟦ u ⟧₂⁻¹⟧₂ ◾ ap (λ x → ⟦⟦ p ⟧₁⁻¹⟧₁ ◾ x ◾ ! ⟦⟦ q ⟧₁⁻¹⟧₁) ⟦ α ⟧₃ ◾ (! ⟦⟦ v ⟧₂⁻¹⟧₂)
\end{code}
}

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
Sabry~\cite{rc2011,James:2012:IE:2103656.2103667,Carette2016} introduced
the~$\Pi$ family of reversible languages based on type isomorphisms and
commutative semiring identities. The fragment without recursive types is
universal for reversible boolean circuits~\cite{James:2012:IE:2103656.2103667}
and the extension with recursive types and trace
operators~\cite{Hasegawa:1997:RCS:645893.671607} is a Turing-complete reversible
language~\cite{James:2012:IE:2103656.2103667,rc2011}. While at first sight,
$\Pi$ might appear \emph{ad hoc},~\cite{Carette2016} shows that it arises
naturally from an ``extended'' view of the Curry-Howard correspondance: rather
than looking at mere \emph{inhabitation} as the main source of analogy between
logic and computation, \emph{type equivalences} becomes the source of analogy.
This allows one to see an analogy between algebra and reversible computation.
Furthermore, this works at multiple levels: that of $1$-algebra (types form a
semiring under isomorphism), but also $2$-algebra (types and equivalences form a
weak Rig Groupoid).  In other words, by taking ``weak Rig Groupoid'' as the
starting semantics, one naturally gets $\Pi$ as the syntax for the language of
proofs of isomorphisms -- in the same way that many terms of the
$\lambda$-calculus arise from Cartesian Closed Categories.

On can also flip this around, and use the $\lambda$-calculus as the
internal language for Cartesian Closed Categories.  However, as Shulman
explains well in his draft book~\cite{shulman} on approaching Categorical
Logic via Type Theory, this works for many other kinds of categories.  As
we are interested in \emph{reversibility}, it is most natural to look at
Groupoids.  Thus $\PiTwo$ represents the simplest non-trivial case of
a (reversible) programming language distilled from such ideas.

What is more surprising is how this also turns out to be a sound
and complete language for describing the univalent universe $\bracket{\bt}$.

\paragraph*{The infinite real projective space \AgdaSymbol{$ℝP^∞$}}

In~\cite{buchholtz2017real}, Buchholtz and Rijke use the ``type of two element
sets'', \AgdaSymbol{Σ[ X ∶ 𝒰 ] ∥ X == $𝕊^0$ ∥}, where \AgdaSymbol{$𝕊^0$} is the
0-sphere, or the 0-iterated suspension of \AgdaSymbol{𝟚}, that is,
\AgdaSymbol{𝟚} itself. They construct the infinite real projective space
\AgdaSymbol{$ℝP^∞$} using universal covering spaces, and show that it is
homotopy equivalent to the Eilenberg-Maclane space \AgdaSymbol{K(ℤ/2ℤ,1)} which
classifies all the 0-sphere bundles. Our reversible programming language is
exactly the syntactic presentation of this classifying space.

If we extend our language to all finite types, we would get a representation of
\AgdaSymbol{Σ[ n ∶ ℕ ] K(ℤ/nℤ, 1)}, which is not well studied classically. Also,
if we choose \AgdaSymbol{$𝕊^1$} instead of \AgdaSymbol{$𝕊^0$}, we get the
infinite complex projective space \AgdaSymbol{$ℂP^∞$}, but it remains to
investigate what kind of reversible programming language this would lead to.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}
\label{sec:conclusion}

What is $\bracket{S^1}$?  Is it useful for programming?  What about $\bracket{\mathbb{N}}$?

What is the ``right'' generalization of $\bracket{-}$ so that we may have all
the usual finite types (such as the ones available in $\Pi$) properly
represented?

\jacques{It is not clear to me that just taking a disjoint union over all the
  types gives the correct generalization.}

Looking at this from the other end: given some ``exotic'' (but finitely
presented) Groupoid $\mathfrak{G}$, is there always a programming language
which is sound and complete for $\mathfrak{G}$ ?

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\bibliographystyle{acm}
{
  \footnotesize
  \bibliography{cites}
}

\end{document}
