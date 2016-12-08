\documentclass[a4paper,USenglish]{lipics-v2016-utf8x}

\usepackage{amsthm,amstext,amssymb,amsmath}
\usepackage[references]{agda} %% \AgdaRef{...}
\usepackage{datetime}
\usepackage{bbold}
\usepackage{url}
\usepackage{xcolor}
\usepackage{multicol}
\usepackage{proof}
\usepackage{stmaryrd}
\usepackage{mathrsfs}
\usepackage{mathabx}
\usepackage{bussproofs}
\usepackage{tikz}
\usepackage{tikz-cd}
\usetikzlibrary{quotes}
\usepackage[section]{placeins}

\newcommand{\amr}[1]{\fbox{\begin{minipage}{0.4\textwidth}\color{purple}{Amr says: #1}\end{minipage}}}
\newcommand{\vic}[1]{\fbox{\begin{minipage}{0.4\textwidth}\color{purple}{Vikraman says: #1}\end{minipage}}}

\newcommand{\hide}[1]{}

\newcommand{\pifrac}{\ensuremath{\Pi^/}}
\newcommand{\iso}{\leftrightarrow}
\newcommand{\isotwo}{\Leftrightarrow}
\newcommand{\alt}{~|~}
\newcommand{\ag}[2]{#1 \sslash #2}
\newcommand{\agp}[3]{#1 \sslash_{#3} #2}
\newcommand{\order}[1]{\hash #1}
\newcommand{\iorder}[1]{1/\hash #1}
\newcommand{\oneg}[1]{\mathbb{1}_{#1}}
\newcommand{\divg}[2]{\hash{#1} \div \hash{#2}}
\newcommand{\ord}[1]{\ensuremath{\mathsf{order}(#1)}}
\newcommand{\inl}[1]{\textsf{inl}(#1)}
\newcommand{\inr}[1]{\textsf{inr}(#1)}
\newcommand{\zt}{\mathbb{0}}
\newcommand{\ot}{\mathbb{1}}
\newcommand{\G}{\mathcal{G}}
\newcommand{\Z}{\mathbb{Z}}
\newcommand{\Zn}{\mathbb{Z}_n}
\newcommand{\Zvn}{\mathbb{Z}^v_n}
\newcommand{\N}{\mathbb{N}}
\newcommand{\cycle}{\textsf{cycle}}
\newcommand{\twod}{\mathbb{T}}
\newcommand{\fract}[2]{#1/#2}
%% \newcommand{\mystrut}{\rule[-0.01\baselineskip]{0pt}{2.2\baselineskip}}
\newcommand{\fv}[2]{\fcolorbox{black}{white}{\strut $#1$}\fcolorbox{black}{gray!20}{$\strut #2$}}
\newcommand{\pt}[2]{\bullet[#1,#2]}
\newcommand{\refl}{\AgdaInductiveConstructor{refl}}
\newcommand{\sing}[1]{\textsc{Sing}(#1)}
\newcommand{\singi}[2]{\textsc{SingI}_{{#1}}(#2)}
\newcommand{\iter}[1]{\textsc{Iter}(#1)}
\newcommand{\pair}[2]{\langle #1,#2 \rangle}
\newcommand{\triple}[3]{\langle #1,#2,#3 \rangle}
\newcommand{\distiterplus}[3]{\mathsf{dist}~#1~#2~#3}

\newcommand{\permone}{\mathit{perm}_{...}}
\newcommand{\permtwo}{\mathit{perm}_{\times\!\times.}}
\newcommand{\permthree}{\mathit{perm}_{.\times\!\times}}
\newcommand{\permfour}{\mathit{perm}_{\rightarrow}}
\newcommand{\permfive}{\mathit{perm}_{\leftarrow}}
\newcommand{\permsix}{\mathit{perm}_{\times.\times}}

\newcommand{\Rule}[4]{
\makebox{{\rm #1}
$\displaystyle
\frac{\begin{array}{l}#2\\\end{array}}
{\begin{array}{l}#3\\\end{array}}$
 #4}}
\newcommand{\proves}{\vdash}
\newcommand{\jdg}[3]{{#1} #3}
\newcommand{\evalone}[2]{#1~\triangleright~#2}
\newcommand{\evaloneb}[2]{#1~\triangleleft~#2}
\newcommand{\unitv}{()}
\newcommand{\unitepl}{\mathsf{{unite_+l}}}
\newcommand{\unitipl}{\mathsf{{uniti_+l}}}
\newcommand{\unitepr}{\mathsf{{unite_+r}}}
\newcommand{\unitipr}{\mathsf{{uniti_+r}}}
\newcommand{\swapp}{\mathsf{{swap_+}}}
\newcommand{\assoclp}{\mathsf{{assocl_+}}}
\newcommand{\assocrp}{\mathsf{{assocr_+}}}
\newcommand{\unitetl}{\mathsf{{unite_{\star}l}}}
\newcommand{\unititl}{\mathsf{{uniti_{\star}l}}}
\newcommand{\unitetr}{\mathsf{{unite_{\star}r}}}
\newcommand{\unititr}{\mathsf{{uniti_{\star}r}}}
\newcommand{\swapt}{\mathsf{{swap_{\star}}}}
\newcommand{\assoclt}{\mathsf{{assocl_{\star}}}}
\newcommand{\assocrt}{\mathsf{{assocr_{\star}}}}
\newcommand{\absorbr}{\mathsf{{absorbr}}}
\newcommand{\absorbl}{\mathsf{{absorbl}}}
\newcommand{\factorzr}{\mathsf{{factorzr}}}
\newcommand{\factorzl}{\mathsf{{factorzl}}}
\newcommand{\dist}{\mathsf{{dist}}}
\newcommand{\factor}{\mathsf{{factor}}}
\newcommand{\distl}{\mathsf{{distl}}}
\newcommand{\factorl}{\mathsf{{factorl}}}
\newcommand{\idiso}{\mathsf{{id}}}

\newcommand{\assocdl}{\mathsf{{assoc_{\odot}l}}}
\newcommand{\assocdr}{\mathsf{{assoc_{\odot}r}}}
\newcommand{\idldl}{\mathsf{{idl_{\odot}l}}}
\newcommand{\idldr}{\mathsf{{idl_{\odot}r}}}
\newcommand{\idrdl}{\mathsf{{idr_{\odot}l}}}
\newcommand{\idrdr}{\mathsf{{idr_{\odot}r}}}
\newcommand{\rinvdl}{\mathsf{{rinv_{\odot}l}}}
\newcommand{\rinvdr}{\mathsf{{rinv_{\odot}r}}}
\newcommand{\linvdl}{\mathsf{{linv_{\odot}l}}}
\newcommand{\linvdr}{\mathsf{{linv_{\odot}r}}}
\newcommand{\idisotwo}{\mathsf{{id}}}
\newcommand{\transtwo}{\bullet}
\newcommand{\respstwo}{\mathsf{{\boxdot}}}
\newcommand{\respptwo}{\mathsf{{resp_{\oplus\Leftrightarrow}}}}
\newcommand{\respttwo}{\mathsf{{resp_{\otimes\Leftrightarrow}}}}
\newcommand{\sumid}{\mathsf{sumid}}
\newcommand{\splitid}{\mathsf{splitid}}
\newcommand{\homps}{\mathsf{hom_{\oplus\odot}}}
\newcommand{\homsp}{\mathsf{hom_{\odot\oplus}}}

\newcommand{\sem}[1]{\llbracket #1 \rrbracket}

%% \theoremstyle{remark}
%\newtheorem{definition}{Definition}
\newtheorem{proposition}{Proposition}
%\newtheorem{example}{Example}
%\newtheorem{lemma}{Lemma}

\renewcommand{\AgdaCodeStyle}{\small}
%% shorten the longarrow
\DeclareUnicodeCharacter{10231}{\ensuremath{\leftrightarrow}}
\DeclareUnicodeCharacter{9678}{$\circledcirc$}
\DeclareUnicodeCharacter{964}{$\tau$}
\DeclareUnicodeCharacter{945}{$\alpha$}
\DeclareUnicodeCharacter{7522}{${}_i$}
\DeclareUnicodeCharacter{8759}{$::$}
\DeclareUnicodeCharacter{737}{${}^{l}$}
\DeclareUnicodeCharacter{931}{$\Sigma$}
\DeclareUnicodeCharacter{8718}{$\qed$}
\DeclareUnicodeCharacter{7503}{${}^k$}
\DeclareUnicodeCharacter{951}{$\eta$}
\DeclareUnicodeCharacter{956}{$\mu$}
\DeclareUnicodeCharacter{8346}{${}_p$}
\DeclareUnicodeCharacter{9679}{$\bullet$}
\DeclareUnicodeCharacter{8703}{\ensuremath{\leftrightarrowtriangle}}
\DeclareUnicodeCharacter{120792}{$\zt$}
\DeclareUnicodeCharacter{120793}{$\ot$}
\DeclareUnicodeCharacter{120795}{$\mathbb{3}$}
\DeclareUnicodeCharacter{10218}{$\langle\!\langle$}
\DeclareUnicodeCharacter{10219}{$\rangle\!\rangle$}
\DeclareUnicodeCharacter{120016}{$\mathcal{A}$}
\DeclareUnicodeCharacter{120057}{$p$}

\makeatletter
\tikzset{my loop/.style =  {to path={
  \pgfextra{\let\tikztotarget=\tikztostart}
  [looseness=8,min distance=5mm, in=240,out=300]
  \tikz@to@curve@path}
  }}
\makeatletter

\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}
module fractypes where
\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{document}

\title{Fractional Types}
\titlerunning{Fractional Types}
\author[1]{Jacques Carette}
\author[2]{Chao-Hong Chen}
\author[3]{Vikraman Choudhury}
\author[4]{Amr Sabry}
\affil[1]{Computing and Software Department, McMaster University,
  Hamilton, Ontario, Canada \\ \texttt{carette@mcmaster.ca}}
\affil[2]{Computer Science Department, Indiana University,
  Bloomington, Indiana, USA \\ \texttt{chen464@indiana.edu}}
\affil[3]{Computer Science Department, Indiana University,
  Bloomington, Indiana, USA \\ \texttt{vikraman@indiana.edu}}
\affil[4]{Computer Science Department, Indiana University,
  Bloomington, Indiana, USA \\ \texttt{sabry@indiana.edu}}

\authorrunning{J. Carette, C.-H. Chen, V. Choudhury and A. Sabry}

\Copyright{Jacques Carette, Chao-Hong Chen, Vikraman Choudhury and Amr Sabry}

\keywords{dummy}
\subjclass{dummy}

\maketitle

\begin{abstract}

%\begin{verbatim}
%Important dates
%----------------
%
%* Abstract submission:            28 November 2016
%* Paper submission:               12 December 2016
%* Notification of acceptance: 12 June 2017
%
%Ok, a plan then:
%
%- we motivate the paper by saying that we sought exactly what we got:
%  using the (now) established definition of 'groupoid cardinality', as
%  well as an (essentially!) standard interpretation of types as
%  groupoids, we exhibit the first types whose natural cardinality is
%  fractional. Which has the advantage of being true!
%
%- admit that we don't quite know what these are useful for (yet). But
%  we can speculate a bit here - perhaps at the end, rather than the
%  start.
%
%- cut out all the stuff that isn't directly a contribution.
%
%- explain the heck out of what we do have.  Be very precise about the
%  background material (on groupoids).  What we have now is a little
%  too fuzzy.
%
%Open questions:
%
%- which way to draw the 'zig-zag' example?  [I have a suggestion, no
%  time to do it right now]
%
%- We use ``value'' and ``term'' interchangeably. Values are canonical
%terms. How do we define canonical terms, esp. for fractional types?
%
%\end{verbatim}

We exhibit types whose natural cardinality is fractional.  More
precisely, we show that the groupoid cardinality (as defined by
Baez-Dolan) of the denotation of the type of a singleton reversible
program $p$ with exactly $k$ distinct proofs of reversibility has
cardinality $1/k$.  We further show that this type is naturally a
multiplicative inverse to the type of all iterates $p ^ i$ of that
reversible program.

We situate this work as an extension of a larger reversible
programming language ($\Pi$), and show that this extension is also
reversible.  Interestingly, this extension supports first-class
functions as well as some natural analogues of operations coming from
compact closed categories.  We emphasize that the key ingredients are
reversibility and proof relevance: cardinality $1/k$ arises from
having exactly $k$ proofs of reversibility.  Our results have been
formalized in Agda.

\end{abstract}

%% \category{CR-number}{subcategory}{third-level}
%% \terms
%% term1, term2
%% \keywords
%% keyword1, keyword2

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction}

\hide{
In Homotopy Type Theory (HoTT)~\cite{hottbook}, types have the
structure of \emph{weak $\omega$-groupoids}. As a first approximation,
we can think of such structures as sets with points (objects) and
paths (equivalences) between the points and higher paths between these
paths and so on. Here are two simple but non-trivial examples:

\medskip
\begin{figure}[h]
\begin{tabular}{c@{\kern -4pt}c}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]
  \draw[dashed] (0,0) ellipse (3cm and 1.2cm);
  \node[below] (A) at (-1.7,0.3) {\texttt{a}};
  \node[below] (B) at (-1.1,0.3) {\texttt{b}};
  \node[below] (C) at (-0.5,0.3) {\texttt{c}};
  \node[below] (D) at (0.5,0.3) {\texttt{d}};
  \node[below] (E) at (1.1,0.3) {\texttt{e}};
  \node[below] (F) at (1.7,0.3) {\texttt{f}};
  \draw[fill] (-1.7,0.3) circle [radius=0.05];
  \draw[fill] (-1.1,0.3) circle [radius=0.05];
  \draw[fill] (-0.5,0.3) circle [radius=0.05];
  \draw[fill] (0.5,0.3) circle [radius=0.05];
  \draw[fill] (1.1,0.3) circle [radius=0.05];
  \draw[fill] (1.7,0.3) circle [radius=0.05];
  \draw (-1.7,0.3) -- (-1.1,0.3);
  \draw (-1.1,0.3) -- (-0.5,0.3);
  \draw (-1.7,0.3) to[bend left] (-0.5,0.3) ;
  \draw (0.5,0.3) -- (1.1,0.3);
  \draw (1.1,0.3) -- (1.7,0.3);
  \draw (0.5,0.3) to[bend left] (1.7,0.3) ;
  \path (A) edge [loop below] node[below] {\texttt{id}} (B);
  \path (B) edge [loop below] node[below] {\texttt{id}} (B);
  \path (C) edge [loop below] node[below] {\texttt{id}} (B);
  \path (D) edge [loop below] node[below] {\texttt{id}} (B);
  \path (E) edge [loop below] node[below] {\texttt{id}} (B);
  \path (F) edge [loop below] node[below] {\texttt{id}} (B);
\end{tikzpicture}
&
\begin{tikzpicture}[scale=0.5,every node/.style={scale=0.5}]
  \draw[dashed] (0,0) ellipse (2cm and 2.4cm);
  \node[below] (B) at (0,-1.1) {\texttt{*}};
  \path (B) edge [loop below] node[below] {\texttt{id}} (B);
  \path (B) edge [loop above, looseness=15, in=48, out=132] node[above] {$p$} (B);
  \path (B) edge [loop above, looseness=25, in=40, out=140] node[above] {$q$} (B);
  \path (B) edge [loop above, looseness=40, in=32, out=148] node[above] {$q'$} (B);
  \path (-1,0.4) edge[double, bend left] node[left] {$\alpha$} (-1,1.0);
\end{tikzpicture}
\end{tabular}
\caption{\label{fig:groupoids}(a) The groupoid $\ag{6}{3}$ \qquad (b) The groupoid $\frac{1}{3}$}
\end{figure}

\medskip\noindent \cite{groupoidcard} assign to each groupoid a
\emph{cardinality} that counts the objects up to equivalences. The
groupoid on the left has six points \texttt{a}, \texttt{b}, \texttt{c},
\texttt{d}, \texttt{e}, and \texttt{f} with two groups of three
points clustered in an equivalence class and hence the groupoid has
cardinality~2. The (2-)groupoid on the right has one point $\ast$ with
four equivalences \texttt{id}, $p$, $q$, and~$q'$ on it. The
equivalences $q$ and $q'$ are however identified by~$\alpha$ leaving
only three distinct equivalence classes and hence making the
cardinality $\frac{1}{3}$.

Both groupoids illustrated in Fig.~\ref{fig:groupoids} involve some
notion of ``division'' that can be captured at the level of types
using a syntactic notion of \emph{fractional types}. In this
introduction, we loosely write $\frac{1}{n}$ for the fractional type
with that cardinality and defer the discussion of the precise syntax
to the technical parts of the paper. The existence of fractional types
that denote groupoids such as the ones depicted in
Fig.~\ref{fig:groupoids} raises an intriguing question about their
applicability to programming practice. In this introduction, we
present, in the context of a new language~$\pifrac$, several
inter-related motivations and applications of fractional types that
are formalized and justified in the remainder of the paper.

\paragraph*{Quotient Types.} Groupoids similar to $\ag{6}{3}$ in
Fig.~\ref{fig:groupoids}(a) intuitively correspond to conventional
\emph{quotient types}. Traditionally~\cite {quotient}, a quotient
type $\ag{T}{E}$ combines a type $T$ with an equivalence relation $E$
that serves as the equality relation on the elements of $T$. Our
notion of fractional types in $\pifrac$ will subsume conventional
quotient types and their applications~\cite{Cohen2013} (e.g.,
defining fractions, multivariate polynomials, field extensions,
algebraic numbers, etc.)

\paragraph*{First-class Equivalence Relations.} Groupoids similar to
$\frac{1}{3}$ in Fig.~\ref{fig:groupoids}(b) can be thought of as a
limiting case of quotient types $\ag{1}{3}$ which consist of just an
equivalence relation. We therefore think of such groupoids as
representing a \emph{first-class} notion of equivalence relations. As
explained in the remainder of the paper, such relations are
represented using programs in $\pifrac$ with the type $1/\hash p$
representing the equivalence relation generated by program $p$. In other
words, instead of just quotient types in which the equivalence
relation is externally defined and hardwired, it is possible to use
existing $\pifrac$ programs to generate and manipulate equivalence
relations as first-class values independently of the types they
eventually act upon. These first-class equivalence relations therefore
enhance~$\pifrac$ with the same expressiveness afforded by the
presence of first-class functions in conventional languages.

\paragraph*{Conservation of Information and Negative Entropy.} A type
with~$N$ elements where $N$ is a non-zero natural number has entropy
$(\log{N})$. This entropy is a measure of information which
materializes itself in memory or bandwidth requirements when storing
or transmitting elements of this type. Thus a type with 8 elements
needs 3 bits of memory for storage or 3 bits of bandwidth for
communication. If quantum field theory is correct (as it so far seems
to be) then information, during any physical process, is neither
created nor
destroyed. Landauer~\cite{Landauer:1961,bennett1985fundamental,Landauer},
Bennet~\cite{Bennett:1973:LRC,bennett2003notes,bennett2010notes},
Fredkin~\cite{fredkin1982conservative} and others made
compelling arguments that this physical principle induces a
corresponding computational principle of ``conservation of
information.'' In the context of finite types, generated from the
empty type $\zt$, the unit type $\ot$, and sums and products $\oplus$
and $\otimes$, this principle states that the foundational (i.e.,
physical) notion of computation is computation via type
isomorphisms~\cite{James:2012:IE:2103656.2103667} or type
equivalences~\cite{Carette2016}, which are both sound and complete
with respect to cardinality-preserving maps. The introduction, in
$\pifrac$, of types (groupoids) with fractional cardinalities
introduces types with \emph{negative entropy}. For example, a type
with cardinality $\frac{1}{8}$ has entropy $\log{\frac{1}{8}} =
-3$. In the context of $\pifrac$ we will interpret this negative
entropy just like we interpret ``negative money,'' as a debt to be
repaid by some other part of the system. This ability to manipulate
negative information as a first-class entity enhances $\pifrac$ with
an expressiveness similar to the one afforded by the presence of
negative numbers (debts and loans) in finance.

\paragraph*{Resource Creation and Annihilation.} In $\pifrac$, all
programs preserve information and hence preserve cardinality. As the
cardinality of the type $n \otimes \frac{1}{n}$ is~1 (for non-zero
$n$), $\pifrac$ has, for example, terms of type $\ot \rightarrow (8
\otimes \frac{1}{8})$.\footnote{As will be explained in the following
sections, the actual type on the right is a dependent type.} Such
terms take the unit type $\ot$ with entropy $\log{1} = 0$ to the type
$8 \otimes \frac{1}{8}$ with entropy $\log{8} + (- \log{8}) = 3 - 3 =
0$. The entropy is globally preserved as desired and expected. But
interestingly, the term introduces, locally, two types that have
entropies of $3$ and $-3$ respectively. Even though the positive and
negative parts must maintain some ``synchronization,'' they can be
further processed independently under some conditions. The most
important condition is that the entire system must be
information-preserving as this ensures that the net positive and
negative entropies must eventually cancel out by a use of a term of
the reverse type $(8 \otimes \frac{1}{8}) \rightarrow \ot$. The
simplest way to appreciate the expressiveness afforded by such a
mechanism is the following credit card analogy. Think of the
computation of type $\ot \rightarrow (8 \otimes \frac{1}{8})$ as
creating, from nothing, an amount of money to be paid to the merchant
instantly, together with a corresponding debt that propagates through
the system. As long as the entire financial system is debt-preserving,
the debt must eventually be reconciled by an equivalent amount of
money (perhaps in another currency) present elsewhere. The underlying
computational process by which such reconciliation happens is
subtle. Briefly speaking, if the positive and negative information are
\emph{treated completely independently}, the computation must involve
some other form of communication to ensure that the amount of money
created matches the amount of money consumed. This other form of
communication can be realized using several familiar computational
effects such as global references, communication channels, or
backtracking. An alternative idea is to capture the ``entanglement''
between the positive and negative information using a precise
dependent type. In this introduction, and in the next section, which
are aimed at conveying high-level ideas and intuitions, we will
explain the basic ideas assuming the positive and negative components
are independent and using an external notion of backtracking to
reconcile them. After introducing the necessary background and
notation, we will develop the necessary formalism to capture the
dependencies using dependent types.

\paragraph*{Correspondence with Commutative Semifields.} Computations
over finite types naturally emerge from viewing types as syntax for
semiring elements, semiring identities as type isomorphisms, and
justifications for semiring identities as program transformations and
optimizations~\cite{Carette2016}. This correspondence provides a rich
proof-relevant version of the Curry-Howard correspondence between
algebra and reversible programming languages. The addition of
fractional types to the mix enriches the correspondence to commutative
semifields, providing a categorification~\cite{math/9802029} of the
non-negative rational numbers in a computational setting.

\paragraph*{Outline.} The remainder of the paper is organized as
follows. We start by presenting two detailed examples that illustrate
the expressiveness of fractional types in a programming
setting. Sec.~3 reviews the necessary background consisting of the
language $\Pi$ for programming in a reversible information-preserving
way. Sec.~4 explains the main novel semantic ideas of using $\Pi$ programs
to generate non-trivial groupoids with fractional cardinality. Sec.~5
translates the semantic ideas into an extension of $\Pi$ with new type
constructors denoting non-trivial groupoids and new programs that
manipulate such types. Sec.~6 presents the operational semantics of
the extended language. The last two sections put our work in
perspective and conclude.

% Conservation of information is our starting point. If your entire
% framework is based on such a conservation principle then you
% \emph{can}, temporarily, introduce \emph{negative information}. This
% negative information will never be duplicated or erased and will
% eventually have to be reconciled. But what could the benefit possibly
% be? The intuition is simple and is essentially closely related to how
% we use credit cards. A credit card creates money and a corresponding
% debt out of nothing. The merchant can get their money and the debt
% propagates through the system until it is reconciled at some later
% point. If the entire system guarantees that the debt will not be
% duplicated or erased, then the net effect is additional convenience
% for everyone. Computationally what his happening is that we have
% created needed resources at one site with a debt: someone must
% eventually provide these resources.

% If quantum field theory is correct (as it so far seems to be) then
% \emph{information}, during any physical process, is neither created
% nor destroyed. Our starting point is this \emph{conservation
%   principle} --- the \emph{conservation of entropy or information},
% adapted to the computational setting, i.e., we study computations
% which are information-preserving. Our initial investigation was in the
% setting of computations over finite types: in that setting
% information-preservation coincides with type isomorphisms,
% permutations on finite sets, and HoTT equivalences. In this paper, we
% extend the work to computations over \emph{groupoids}.

% In both the situation with finite sets and groupoids, our measure of
% information is the same. With each type $T$ (finite set or groupoid)
% of cardinality $n$, we associate the information measure
% $H(T) = \log{n}$. One way to think of $H(T)$ is that it is a measure
% of how much space it takes to store values in $T$, not knowing
% anything about their distribution. For non-empty finite sets,
% $\log{n}$ is always a natural number representing the number of bits
% necessary to store values of type $T$. For groupoids, it is possible
% to have non-negative rational numbers as their cardinality, e.g.,
% $\frac{1}{3}$, which would give us \emph{negative} entropy,
% information, or space.

% An important paper about negative entropy in the context of the
% Landauer limit and reversible computation:
% \url{http://www.nature.com/nature/journal/v474/n7349/full/nature10123.html}

% Something else about negative entropy
% \url{https://en.wikipedia.org/wiki/Negentropy}: In information theory
% and statistics, negentropy is used as a measure of distance to
% normality. Out of all distributions with a given mean and variance,
% the normal or Gaussian distribution is the one with the highest
% entropy. Negentropy measures the difference in entropy between a given
% distribution and the Gaussian distribution with the same mean and
% variance.

% One more link about negative entropy
% \url{https://www.quora.com/What-does-negative-entropy-mean}: For
% example, if you burn fuel, you get water, CO2 and some other
% wastes. Could be possible on a lab transform water + CO2 + some other
% wastes on fuel again? Of course yes, but the energy to make that is
% much more than the energy that you could obtain again from the
% reconstructed fuel. If you see the local process (I've converted
% water+ CO2 + some other wastes on fuel) the entropy is clearly
% negative. But if you consider the energy necessary to achieve that the
% global entropy is clearly positive.

% Something about negative information:
% \url{http://www.ucl.ac.uk/oppenheim/negative-information_p2.html}

% In terms of space, we interpret a negative amount as the ability to
% reclaim that much space.

% Since information is defined using cardinality, the conclusion is that
% we will consider computations between types $T_1$ and $T_2$ (finite
% sets or groupoids) such that the cardinality of $T_1$ is the same as
% the cardinality of $T_2$.
}

\hide{
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Examples}

We present two examples that illustrate the novelty of fractional
types in a programming context. The first example is of a denotational
flavor showing how to decompose types into components that could be
processed concurrently. The second example, of a more operational
flavor, illustrates the main ideas involved in executing the credit
card analogy from the introduction.

%%%%%
\subsection{$\sqrt{n}$ Speedup}

Say we want to add 1 $\pmod{100}$ to numbers in the range
$[0..99]$. One approach is to represent the input type as a monolithic
type with 100 constructors giving us a unary representation of the
numbers. The addition function in this case will have 100 cases, one
for each possible input, and might, in the worst case, take 100 steps
to compute the successor of a number. A better approach is to
represent the input type as the product of two types, of
cardinality~10 each, giving us a decimal representation of the
numbers. The addition function in this case will take a maximum of 20
steps: 10 to calculate the successor of the digit in the unit position
and, in case of a carry, another 10 to calculate the successor of the
digit in the tens position. In a conventional setting, this idea works
perfectly but only if the input cardinality~$n$ has factors near
$\sqrt{n}$: it is completely useless if the input cardinality~$n$ is a
prime number.

Yet we can make this idea work with fractional types even if the
cardinality is prime. Here is an example in which we will decompose a
type with 7 elements into the product of two types with cardinality
$2 \frac{1}{3}$ and 3 respectively. Let $C$ be the following type with
7 elements:
\begin{center}
\begin{tikzpicture}[scale=0.5,every node/.style={scale=0.5}]
  \draw[dashed] (0,0) ellipse (7.2cm and 1.2cm);
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
\end{tikzpicture}
\end{center}
\noindent The labels on the objects are meant to be mnemonic: formally the objects
would correspond to various iterations of some program.

The first step is to write a \emph{reversible} program $p$
that represents a permutation of $C$ of order 3. For example:
\[\begin{array}{rcl@{\qquad\qquad\qquad}rcl}
p(\texttt{sun}) &=& \texttt{mon} &
                                   p(\texttt{mon}) &=& \texttt{tue} \\
p(\texttt{tue}) &=& \texttt{sun} &
                                   p(\texttt{wed}) &=& \texttt{thu} \\
p(\texttt{thu}) &=& \texttt{fri} &
                                   p(\texttt{fri}) &=& \texttt{wed} \\
p(\texttt{sat}) &=& \texttt{sat}
\end{array}\]

\noindent Clearly applying $p$ three consecutive times yields the
identity function. We express this fact by saying $\ord{p} = 3$. It
follows that $p^0$ is equivalent to $p^3, p^{-3}, p^6, \ldots$, that
$p^1$ is equivalent to $p^4, p^{-2}, p^7, p^{-5}, \ldots$, and that
$p^2$ is equivalent to $p^5, p^{-1}, p^8, p^{-4}, \ldots$ where the
negative powers are interpreted as applying the program in
reverse. Furthermore we have that composing $p^i$ and $p^j$ is the
identity if $i+j \equiv 0\pmod{3}$.

As explained in Sec.~\ref{sec:groupoids}, the definition of any $p$
representing a permutation of order $o$ will induce two groupoids of
cardinality $o$ and $1/o$. In our case, we get:
\begin{itemize}
\item a first groupoid which we denote by $\order{p}$ and which has (up
  to equivalence) three clusters of objects corresponding to each
  distinct (up to equivalence) iteration of $p$. (We omit the identity
  arrows in the figure.) It has cardinality $3$:
\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.8}]
  \draw[dashed] (0,-0.2) ellipse (3cm and 0.7cm);
  \node[below] at (-2,0) {$p^0$};
  \node[below] at (0,0) {$p^1$};
  \node[below] at (2,0) {$p^2$};
  \draw[fill] (-2,0) circle [radius=0.05];
  \draw[fill] (0,0) circle [radius=0.05];
  \draw[fill] (2,0) circle [radius=0.05];
\end{tikzpicture}
\end{center}
\item a second groupoid which we denote by $1/\hash p$ and which has one
  trivial object and an equivalence for each distinct iteration of~$p$
  showing that it can be annihilated to the identity by composing it
  with its inverse. (We explicitly include the identity arrow to
  emphasize that there are three distinct equivalences):
\begin{center}
\begin{tikzpicture}[scale=0.4,every node/.style={scale=0.4}]
  \draw[dashed] (0,0) ellipse (1.5cm and 2.1cm);
  \node[below] (B) at (0,-0.7) {$\ast$};
  \path (B) edge [loop below] node[below] {$p^0$} (B);
  \path (B) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (B);
  \path (B) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (B);
\end{tikzpicture}
\end{center}
\end{itemize}

Assuming, for simplicity in this section, that positive and negative
information may be processed completely independently, the trivial one
point groupoid has the same cardinality as $\order{p} ~\otimes~
1/\hash p$ for any $p$. Indeed taking the product of the particular
groupoids $\order{p}$ and $1/\hash p$ above produces the groupoid:

\begin{center}
\begin{tikzpicture}[scale=0.4,every node/.style={scale=0.4}]
  \draw[dashed] (0,-0.3) ellipse (7cm and 2.7cm);
  \node[below] (1) at (-3.5,-1) {$p^0$};
   \node[below] (2) at (0,-1) {$p^1$};
  \node[below] (3) at (3.5,-1) {$p^2$};
  \draw[fill] (-3.5,-1) circle [radius=0.05];
  \draw[fill] (0,-1) circle [radius=0.05];
  \draw[fill] (3.5,-1) circle [radius=0.05];

  \path (1) edge [loop below] node[below] {$p^0$} (1);
  \path (1) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (1);
  \path (1) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (1);

  \path (2) edge [loop below] node[below] {$p^0$} (2);
  \path (2) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (2);
  \path (2) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (2);

  \path (3) edge [loop below] node[below] {$p^0$} (3);
  \path (3) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (3);
  \path (3) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (3);
\end{tikzpicture}
\end{center}
\noindent which has cardinality 1. This justifies the following
cardinality-preserving transformations on $C$:
\[\begin{array}{rcl}
C &≃&  C \otimes \ot \\
&≃& C \otimes (\order{p} \otimes 1/\hash p) \\
&≃& (C \otimes 1/\hash p) \otimes \order{p}
\end{array}\]
which decomposes $C$ into the product of $C \otimes 1/\hash p$ and
$\order{p}$. The latter groupoid has cardinality 3. The first groupoid,
depicted below, has cardinality $2\frac{1}{3}$. (We omit the identity
arrows to avoid excessive clutter):

\begin{center}
\begin{tikzpicture}[scale=0.4,every node/.style={scale=0.4}]
  \draw[dashed] (0,-0.5) ellipse (9cm and 2.7cm);
  \node[below] (1) at (-6,-1.5) {\texttt{sun}};
   \node[below] (2) at (-4,-1.5) {\texttt{mon}};
  \node[below] (3) at (-2,-1.5) {\texttt{tue}};
  \node[below] (4) at (0,-1.5) {\texttt{wed}};
  \node[below] (5) at (2,-1.5) {\texttt{thu}};
  \node[below] (6) at (4,-1.5) {\texttt{fri}};
  \node[below] (7) at (6,-1.5) {\texttt{sat}};
  \draw[fill] (-6,-1.5) circle [radius=0.05];
  \draw[fill] (-4,-1.5) circle [radius=0.05];
  \draw[fill] (-2,-1.5) circle [radius=0.05];
  \draw[fill] (0,-1.5) circle [radius=0.05];
  \draw[fill] (2,-1.5) circle [radius=0.05];
  \draw[fill] (4,-1.5) circle [radius=0.05];
  \draw[fill] (6,-1.5) circle [radius=0.05];

%%  \path (1) edge [loop above] node[above] {$p^0$} (1);
  \path (1) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (1);
  \path (1) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (1);

%%  \path (2) edge [loop above] node[above] {$p^0$} (2);
  \path (2) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (2);
  \path (2) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (2);

%%  \path (3) edge [loop above] node[above] {$p^0$} (3);
  \path (3) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (3);
  \path (3) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (3);

%%  \path (4) edge [loop above] node[above] {$p^0$} (4);
  \path (4) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (4);
  \path (4) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (4);

%%  \path (5) edge [loop above] node[above] {$p^0$} (5);
  \path (5) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (5);
  \path (5) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (5);

%%  \path (6) edge [loop above] node[above] {$p^0$} (6);
  \path (6) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (6);
  \path (6) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (6);

%%  \path (7) edge [loop above] node[above] {$p^0$} (7);
  \path (7) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (7);
  \path (7) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (7);
\end{tikzpicture}
\end{center}

%%%%%
\subsection{Credit Card Computation}

We illustrate the creation and annihilation of values with the
following small example. Let $\textsf{swap}$ be the permutation that
swaps two elements: it has order 2, i.e., $\textsf{swap}^0 =
\textsf{swap}^2 = \textsf{swap} \odot \textsf{swap} = \textsf{id}$
where $\odot$ is the sequential composition of programs. As explained
in the previous section, this permutation introduces two types
$\order{\textsf{swap}}$ and $1/\hash \textsf{swap}$ of cardinality 2
and $\frac{1}{2}$ respectively. The first type $\order{\textsf{swap}}$
has, up to equivalence, two values $\textsf{swap}^0$ (or
$\textsf{id}$) and $\textsf{swap}^1$ (or just $\textsf{swap})$. In the
case of dependent types explained later, the second type
$\iorder{\textsf{swap}}$ will have one value $\alpha$ which can
annihilate either of the values in $\order{\textsf{swap}}$ by
composing them with the right 1-combinator to produce the identity. In
the current presentation using non-dependent types, we will think of
$\alpha$ as having two instances: one $\alpha_{\idiso}$ which can
annihilate \textsf{id} and one $\alpha_{\textsf{swap}}$ which can
annihilate \textsf{swap}. Given these ingredients, we can write the
following program in $\pifrac$:

\begin{center}
\begin{tikzpicture}[scale=0.9,every node/.style={scale=0.9}]
  \draw (0,0) -- (1,0) -- (1,2) -- (0,2) -- cycle;
  \path (-1.1,1) edge node[above] {$\order{\textsf{swap}}$} (0,1);
  \path (1,1.8) edge node[above] {$\ot$} (1.6,1.8);
  \path (1,0.2) edge node[above] {$\order{\textsf{swap}}$} (4,0.2);
  \draw (1.6,0.8) -- (2.6,0.8) -- (2.6,2.8) -- (1.6,2.8) -- cycle;
  \path (2.6,2.6) edge node[above] {$\order{\textsf{swap}}$} (6,2.6);
  \path (2.6,1) edge node[above] {$1/\hash\textsf{swap}$} (4,1);
  \draw (4,0) -- (5,0) -- (5,2) -- (4,2) -- cycle;
  \path (5,1) edge node[above] {$\ot$} (6,1);
  \draw (6,0.8) -- (7,0.8) -- (7,2.8) -- (6,2.8) -- cycle;
  \path (7,1.8) edge node[above] {$\order{\textsf{swap}}$} (8,1.8);
  \node at (0.5,1) {$\textsf{unit}_\times$};
  \node at (2.1,1.8) {$\eta_{\textsf{swap}}$};
  \node at (4.5,1) {$\epsilon_{\textsf{swap}}$};
  \node at (6.5,1.8) {$\textsf{unit}_\times$};
\end{tikzpicture}
\end{center}

\noindent In the figure, the wires are labeled by the types of the
values they may carry and the boxes are cardinality-preserving
primitives in the language. A good approximation of their types for
the purposes of this section is:

\[\begin{array}{rcccl}
\tau &:& \textsf{unit}_\times &:& \tau \otimes \ot \\
\ot &:& \eta_{\textsf{swap}} &:& \order{\textsf{swap}} \otimes 1/\hash \textsf{swap} \\
\order{\textsf{swap}} \otimes 1/\hash \textsf{swap} &:& \epsilon_{\textsf{swap}} &:& \ot
\end{array}\]

As is common in string diagrams for
categories~\cite{selinger-graphical}, we elide associativity in the
figure. When $\eta_{\textsf{swap}}$ executes, it consumes the unique
value of type $\ot$ and it must produce a pair of values of the given
types. To maintain reversibility, the only choices are a program and
the equivalence that annihilates it so the choices are limited to
$(\idiso,\alpha_{\idiso})$ and
$(\textsf{swap},\alpha_{\textsf{swap}})$. At this point, there is not
enough information to commit to either choice. The situation is
analogous to several classical ones which involve speculative
computation and can be resolved using the same techniques. One
possibility is to speculatively choose a pair of values and backtrack
if the choice proves incorrect. In the following we use this
backtracking approach in which $\eta_{\textsf{swap}}$ speculatively
chooses $(\idiso,\alpha_{\idiso})$ as its initial value and adjusts
its choice if it is not consistent with the upstream constraints. Once
the types of the constructs are made dependent, the implementation can
avoid backtracking and use the dataflow dependencies to reconcile the
values as shown in Sec.~6. For now, there are two execution scenarios
depending on which input is given to the circuit. If the input is
$\textsf{swap}$, we have the following situation:

\begin{center}
\begin{tikzpicture}[scale=0.9,every node/.style={scale=0.9}]
  \draw (0,0) -- (1,0) -- (1,2) -- (0,2) -- cycle;
  \path [->] (-1.1,1) edge node[above] {$\order{\textsf{swap}}$}
                                 node[below,red] {$\textsf{swap}$} (0,1);
  \path [->]  (1,1.8) edge node[above] {$\ot$}
                               node[below,red] {$()$} (1.6,1.8);
  \path [->]  (1,0.2) edge node[above] {$\order{\textsf{swap}}$}
                               node[below,red] {$\textsf{swap}$} (4,0.2);
  \draw (1.6,0.8) -- (2.6,0.8) -- (2.6,2.8) -- (1.6,2.8) -- cycle;
  \path [->]  (2.6,2.6) edge node[above] {$\order{\textsf{swap}}$}
                                  node[below,red] {$\idiso$} (6,2.6);
  \path [->]  (2.6,1) edge node[above] {$1/\hash\textsf{swap}$}
                               node[below,red] {$\alpha_{\idiso}$} (4,1);
  \draw [blue,thick] (4,0) -- (5,0) -- (5,2) -- (4,2) -- cycle;
  \path (5,1) edge node[above] {$\ot$} (6,1);
  \draw (6,0.8) -- (7,0.8) -- (7,2.8) -- (6,2.8) -- cycle;
  \path  (7,1.8) edge node[above] {$\order{\textsf{swap}}$} (8,1.8);
  \node at (0.5,1) {$\textsf{unit}_\times$};
  \node at (2.1,1.8) {$\eta_{\textsf{swap}}$};
  \node at (4.5,1) {$\epsilon_{\textsf{swap}}$};
  \node at (6.5,1.8) {$\textsf{unit}_\times$};
\end{tikzpicture}
\end{center}

\noindent In the figure, the values of each type are shown in red under
the corresponding wire. Execution proceeds until the active
combinator $\epsilon_{\textsf{swap}}$ (shown in blue). This combinator
receives a pair of mismatched values which it cannot
annihilate. It therefore reverses execution to force
$\eta_{\textsf{swap}}$ to alter its choice:

\begin{center}
\begin{tikzpicture}[scale=0.9,every node/.style={scale=0.9}]
  \draw (0,0) -- (1,0) -- (1,2) -- (0,2) -- cycle;
  \path [->] (-1.1,1) edge node[above] {$\order{\textsf{swap}}$}
                                 node[below,red] {$\textsf{swap}$} (0,1);
  \path [->] (1,1.8) edge node[above] {$\ot$}
                               node[below,red] {$()$} (1.6,1.8);
  \path [<-] (1,0.2) edge node[above] {$\order{\textsf{swap}}$}
                               node[below,red] {$\textsf{swap}$} (4,0.2);
  \draw [blue,thick] (1.6,0.8) -- (2.6,0.8) -- (2.6,2.8) -- (1.6,2.8) -- cycle;
  \path [<-] (2.6,2.6) edge node[above] {$\order{\textsf{swap}}$} (6,2.6);
  \path [<-] (2.6,1) edge node[above] {$1/\hash\textsf{swap}$} (4,1);
  \draw (4,0) -- (5,0) -- (5,2) -- (4,2) -- cycle;
  \path (5,1) edge node[above] {$\ot$} (6,1);
  \draw (6,0.8) -- (7,0.8) -- (7,2.8) -- (6,2.8) -- cycle;
  \path (7,1.8) edge node[above] {$\order{\textsf{swap}}$} (8,1.8);
  \node at (0.5,1) {$\textsf{unit}_\times$};
  \node at (2.1,1.8) {$\eta_{\textsf{swap}}$};
  \node at (4.5,1) {$\epsilon_{\textsf{swap}}$};
  \node at (6.5,1.8) {$\textsf{unit}_\times$};
\end{tikzpicture}
\end{center}

\noindent When $\eta_{\textsf{swap}}$ is approached in the reverse
direction, it updates its guess to
$(\textsf{swap},\alpha_{\textsf{swap}})$ and resumes forward
execution. This guess proves to be the correct one to match the input
value and the entire circuit terminates with the value
$\textsf{swap}$. Of course the initial input could have been $\idiso$
in which case no backtracking would have been needed. The setup
generalizes to arbitrary reversible programs $p$ with finite order:
the back-and-forth negotiation is guaranteed to terminate as there
are only a finite number of possible choices for each value.
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Body of the paper split into smaller files

%% Sec 3
\input{pibackground.tex}
%% Sec 4
\input{groupoid.tex}
%% Sec 5 A new language with fractional types and its denotational semantics (mostly reference to sec 4)
\input{pifrac.tex}
%% Sec 6 its operational semantics + pragmatics
\input{opsem.tex}
%% Sec 7 limitations; open problems
\input{limitations.tex}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}

We have presented a natural notion of \emph{fractional types} that
enriches a class of reversible programming languages in several
dimensions.  Further research might show how to use fractional
types in a conventional (i.e., irreversible) programming language, their full
potential is only achieved when the ambient language guarantees that
no information is created or erased.

The key semantic insight is that iterating a reversible program $p$ on
a finite type must eventually reach the identity in $\ord{p}$
steps. By being careful not to collapse proofs, each such reversible
program has $\ord{p}$ distinct proofs of reversibility and hence gives
rise to a groupoid with cardinality $\frac{1}{\ord{p}}$. Going from
this observation to a full programming language required several
difficult and subtle design choices which we have explored to produce
$\Pi^/$. The latter language has a natural denotational semantics
where types denote groupoids. Its operational semantics requires a
mechanism to express a computational effect which enables spatially
separated parts of the program to communicate in a way that is
reminiscent of entanglement in quantum mechanics. It is possible to
realize such an operational semantics using global reference cells,
backtracking, or other conventional technique. A more enlightening and
less ad hoc implementation encodes the required dependency in dataflow
constraints encoded in dependent types. The key idea is to generalize
the usual cartesian product to a \emph{tangled product} that allows the
components to interact at synchronization points.

Our fractional types extend the natural denotation of types from sets
to non-trivial groupoids but they only scratch the surface of the
tower of weak $\omega$-groupoids that is expressible in HoTT. A long
term goal of our research is to find natural type constructors
inspired by the rich combinatorial structure of weak
$\omega$-groupoids and that provide novel programming abstractions.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\input{appendix.tex}

\bibliographystyle{plainurl}
\bibliography{cites}

\end{document}
