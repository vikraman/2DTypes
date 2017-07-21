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

\newcommand{\byiso}[1]{{\leftrightarrow}{\langle} ~#1~ \rangle}
\newcommand{\byisotwo}[1]{{\Leftrightarrow}{\langle} ~#1~ \rangle}
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
\newcommand{\iso}{\leftrightarrow}
\newcommand{\isotwo}{\Leftrightarrow}
\newcommand{\isothree}{\Lleftarrow \! \! \! \! \Rrightarrow}
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

In this paper we report on a formal connection between appropriately formulated
reversible languages on one hand and univalent universes on the other. In the
next section, we give a rational reconstruction of $\Pi$ focusing on a small
``featherweight'' fragment. In Sec.~\ref{sec:univalent}, we review
\emph{univalent fibrations} which allow us to give formal presentations of
``small'' univalent universes. In Sec.~\ref{sec:correspondence} we state and prove
the formal connection between the systems presented in the preceding two
sections. Sec.~\ref{sec:conclusion} puts our work in a larger context, discusses
related and future work, and concludes.

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
\AgdaFunction{controlled}  &:& \forall a.~ (a \leftrightarrow a) \quad\rightarrow
                            & ~(\bt \otimes a \leftrightarrow \bt \otimes a) \\
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
\AgdaFunction{not} &:& \bt \leftrightarrow \bt \\
\AgdaFunction{not} &=&
  \AgdaFunction{unfoldBool} \odot \AgdaFunction{swap₊} \odot \AgdaFunction{foldBool} \\
\\
\AgdaFunction{cnot} &:& \bt \otimes \bt \leftrightarrow \bt \otimes \bt \\
\AgdaFunction{cnot} &=& \AgdaFunction{controlled}~\AgdaFunction{not} \\
\\
\AgdaFunction{toffoli} &:& \bt \otimes (\bt \otimes \bt)
                           \leftrightarrow  \bt \otimes (\bt \otimes \bt) \\
\AgdaFunction{toffoli} &=& \AgdaFunction{controlled}~\AgdaFunction{cnot} \\
\end{array}\]}
%%%

\noindent While we wrote \AgdaFunction{controlled} in equational-reasoning
style, \AgdaFunction{not} is written in the point-free combinator style.  These
are equivalent as $\byiso{-}$ is defined in terms of the sequential composition
combinator $\odot$.

As is customary in any semantic perspective on programming languages, we are
interested in the question of when two programs are ``equivalent.'' Consider the
following six programs of type~$\bt \leftrightarrow \bt$:

{\small
\[\def\arraystretch{1.2}\begin{array}{rcl}
\AgdaFunction{id₁}~\AgdaFunction{id₂}~\AgdaFunction{id₃}~
  \AgdaFunction{not₁}~\AgdaFunction{not₂}~\AgdaFunction{not₃} &:& \bt \leftrightarrow \bt \\
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
\AgdaFunction{notOpt} &:& \AgdaFunction{not₃} \Leftrightarrow \AgdaFunction{not} \\
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
type, the type of booleans:

% \jacques{the code above uses $\odot$ for 1-composition,
% $\boxdot$ for parallel 2-composition of $\odot$, while the
% code below uses $\circ$ and $\odot$ respectively, which is
% quite confusing.  We should pick one notation.}

\[\def\arraystretch{0.8}\begin{array}{l@{\quad}rclrl}
(\textit{Types}) & \tau &::=& \bt \\
\\
(\textit{Terms}) &  v &::=& \fc &:& \bt \\
              && \alt & \tc &:& \bt \\
\\
 (\textit{1-combinators}) &  c &::=& \id &:& \tau \iso \tau \\
               && \alt & \swap &:& \bt \iso \bt \\
               && \alt & ! &:& (\tau_1 \iso \tau_2) \to (\tau_2 \iso \tau_1) \\
               && \alt & \odot &:& (\tau_1 \iso \tau_2) \to (\tau_2 \iso \tau_3) \to (\tau_1 \iso \tau_3)  \\
\\
(\textit{2-combinators}) & \alpha &::=& \id &:& c \isotwo c \\
            && \alt & \idlc &:& \compc{\id}{c} \isotwo c \\
            && \alt & \idrc &:& \compc{c}{\id} \isotwo c \\
            && \alt & \invl &:& \compc{c\;}{\;\invc{c}} \isotwo \id \\
            && \alt & \invr &:& \compc{\invc{c}}{c} \isotwo \id \\
            && \alt & \rho &:& \swap \circ \swap \isotwo \id \\
            && \alt & \assocc &:&
                                  \compc{(\compc{c_1}{c_2})}{c_3} \isotwo \compc{c_1}{(\compc{c_2}{c_3})} \\
            && \alt & \boxdot &:& (c_1 \isotwo c_1') \to (c_2 \isotwo c_2') \to
                             (\compc{c_1}{c_2} \isotwo \compc{c_1'}{c_2'}) \\
            && \alt & !! &:& (c_1 \isotwo c_2) \to (c_2 \isotwo c_1) \\
            && \alt & \bullet &:& (c_1 \isotwo c_2) \to (c_2 \isotwo c_3) \to (c_1 \isotwo c_3)
\end{array}\]

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
  Given a 1-combinator $c : \tau \leftrightarrow \tau$, we either have a
  2-combinator of type $c \Leftrightarrow \id$ or a 2-combinator of type
  $c \Leftrightarrow \swap$. In other words, every 1-combinator has a canonical
  representation as either $\id$ or $\swap$ and the set of 2-combinators is rich
  enough to normalize $c$ to its canonical representation.
\end{lemma}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Univalent Fibrations}
\label{sec:univalent}

\AgdaHide{
\begin{code}
  {-# OPTIONS --without-K --type-in-type --allow-unsolved-metas #-}

  𝒰 = Set

  record Σ (A : 𝒰) (B : A → 𝒰) : 𝒰 where
    constructor _,_
    field
      pr₁ : A
      pr₂ : B pr₁

  open Σ public
  infixr 4 _,_
  syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

  infix 2 _×_
  _×_ : (A B : 𝒰) → 𝒰
  A × B = Σ A (λ _ → B)

  id : {A : 𝒰} → A → A
  id a = a

  infix 4 _∘_
  _∘_ : {A : 𝒰} {B : A → 𝒰} {C : {a : A} → B a → 𝒰}
      → (g : {a : A} → (b : B a) → C b) (f : (a : A) → B a)
      → (a : A) → C (f a)
  g ∘ f = λ a → g (f a)

  data _==_ {A : 𝒰} : A → A → 𝒰 where
    refl : (a : A) → a == a

  infix 3 _∼_
  _∼_ : {A : 𝒰} {B : A → 𝒰} (f g : (a : A) → B a) → 𝒰
  _∼_ {A} f g = (a : A) → f a == g a

  ap : {A B : 𝒰} {x y : A} → (f : A → B) (p : x == y) → f x == f y
  ap f (refl x) = refl (f x)

  transport : {A : 𝒰} (P : A → 𝒰) {x y : A} → x == y → P x → P y
  transport P (refl x) u = u

  PathOver : {A : 𝒰} (P : A → 𝒰) {x y : A} (p : x == y) (u : P x) (v : P y) → 𝒰
  PathOver P p u v = transport P p u == v

  syntax PathOver P p u v = u == v [ P ↓ p ]
\end{code}
}

We work in intensional type theory with one univalent universe closed
under propositional truncation.

\subsection{Equivalences}

Given types \AgdaSymbol{A} and \AgdaSymbol{B}, a function \AgdaSymbol{f
: A → B} is an quasi-inverse, if
%
\begin{code}
  is-qinv : {A B : 𝒰} → (f : A → B) → 𝒰
  is-qinv {A} {B} f = Σ[ g ∶ (B → A) ] (g ∘ f ∼ id × f ∘ g ∼ id)
\end{code}
%
To make this type contractible, we need to adjointify it.
%
\begin{code}
  is-hae : {A B : 𝒰} → (f : A → B) → 𝒰
  is-hae {A} {B} f = Σ[ g ∶ (B → A) ] Σ[ η ∶ g ∘ f ∼ id ]
                     Σ[ ε ∶ f ∘ g ∼ id ] (ap f ∘ η ∼ ε ∘ f)
\end{code}
%
Then we can define a type of equivalences between two types.
%
\begin{code}
  _≃_ : (A B : 𝒰) → 𝒰
  A ≃ B = Σ[ f ∶ (A → B) ] is-hae f
\end{code}

\subsection{Type Families are Fibrations}

A type family \AgdaSymbol{P} over a type \AgdaSymbol{A} is a fibration
with base space \AgdaSymbol{A}, and \AgdaSymbol{P x} the fiber over
\AgdaSymbol{x}. The total space is given by \AgdaSymbol{Σ[ x ∶ A ] P
x}. The path lifting property can be defined by path induction.
%
\begin{code}
  lift : {A : 𝒰} {P : A → 𝒰} {x y : A}
       → (u : P x) (p : x == y)
       → (x , u) == (y , transport P p u)
  lift u (refl x) = refl (x , u)
\end{code}

\subsection{Paths to Equivalences}

The \AgdaSymbol{transport} operation lifts paths to equivalences. By
transporting identity, we can convert a path to an equivalence.

\begin{code}
  idh : {A : 𝒰} {P : A → 𝒰} → (f : (a : A) → P a) → f ∼ f
  idh f a = refl (f a)

  ide : (A : 𝒰) → A ≃ A
  ide A = id , id , idh id , idh id , idh (idh id)

  tpt-eqv : {A : 𝒰} (P : A → 𝒰) → {a b : A} → a == b → P a ≃ P b
  tpt-eqv P (refl a) = ide (P a)

  idtoeqv : {A B : 𝒰} → A == B → A ≃ B
  idtoeqv = tpt-eqv id
\end{code}

\subsection{Univalent Fibrations}

A type family (fibration) \AgdaSymbol{P : A → 𝒰} is univalent, iff equivalences
in the base space are \emph{equivalent} to equivalences in the fiber.

\begin{code}
  is-univ-fib : {A : 𝒰} (P : A → 𝒰) → 𝒰
  is-univ-fib {A} P = (a b : A) → is-hae (tpt-eqv P {a} {b})
\end{code}

In particular, the univalence axiom is a specialization of this to the
constant fibration. We say that a universe is univalent if it
satisfies univalence. \VC{Tarski universes later}

\begin{code}
  is-univalent : 𝒰
  is-univalent = is-univ-fib id
\end{code}

\subsection{Propositional Truncation as an HIT}

We define propositional truncation as a higher inductive type as follows.

\begin{code}
  postulate
    ∥_∥ : (A : 𝒰) → 𝒰
    ∣_∣ : {A : 𝒰} → (a : A) → ∥ A ∥
    ident : {A : 𝒰} {a b : ∥ A ∥} → a == b
\end{code}

Truncating a type makes it a proposition.

\begin{code}
  is-contr : (A : 𝒰) → 𝒰
  is-contr A = Σ A (λ a → (b : A) → (a == b))

  is-prop : 𝒰 → 𝒰
  is-prop A = (a b : A) → a == b

  ∥-∥-is-prop : {A : 𝒰} → is-prop ∥ A ∥
  ∥-∥-is-prop _ _ = ident
\end{code}

We can only eliminate a propositional truncation to a proposition.

\begin{code}
  postulate
    rec-∥-∥ : {A : 𝒰} (P : 𝒰)
            → (A → P) → is-prop P
            → ∥ A ∥ → P
    ind-∥-∥ : {A : 𝒰} (P : ∥ A ∥ → 𝒰)
            → ((a : A) → P ∣ a ∣)
            → ((a : ∥ A ∥) → is-prop (P a))
            → (a : ∥ A ∥) → P a
\end{code}

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

Soundness; completeness; etc.

We add a new level to $\PiTwo$ to prove the full correspondence of the first 2-levels of $\PiTwo$ and $\{\bt\}$:
\[\def\arraystretch{0.8}\begin{array}{l@{\quad}rclrl}
(\textit{3-combinators}) & \xi &::=& \trunc &:& (\alpha, \beta : c_1 \isotwo c_2) \to \alpha \isothree \beta
\end{array}\]

\begin{theorem}[Soundness and completeness for $\PiTwo$]
  There exist functions $\dbracket{ \_ }_n$ which map n-combinator in $\PiTwo$ to n-path in $\{\bt\}$,
  such that
  \begin{enumerate}
  \item For all 1-combinators $p, q$, $p \iso q$ iff $\dbracket{ p }_1 = \dbracket{ q }_1$.
  \item For all 2-combinators $\alpha, \beta$, $\alpha \isotwo \beta$ iff $\dbracket{ \alpha }_2 = \dbracket{ \beta }_2$.
  \end{enumerate}
\end{theorem}

\begin{theorem}[Soundness and completeness for $\{\bt\}$]
  There exist functions $\dbracket{ \_ }_n^{-1}$ which map n-path in $\{\bt\}$ to n-combinator in $\PiTwo$,
  such that
  \begin{enumerate}
  \item For all 1-paths $p, q$, $p \equiv q$ iff $\dbracket{ p }_1^{-1} \isotwo \dbracket{ q }_1^{-1}$.
  \item For all 2-paths $\alpha, \beta$, $\alpha \equiv \beta$ iff $\dbracket{ \alpha }_2^{-1} \isothree \dbracket{ \beta }_2^{-1}$.
  \end{enumerate}
\end{theorem}

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
explains well in his draft book~\cite{Shullman} on approaching Categorical
Logic via Type Theory, this works for many other kinds of categories.  As
we are interested in \emph{reversibility}, it is most natural to look at
Groupoids.  Thus $\PiTwo$ represents the simplest non-trivial case of
a (reversible) programming language distilled from such ideas.

What is more surprising is how this also turns out to be a sound
and complete language for describing the univalent universe $\bracket{\bt}$.

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
