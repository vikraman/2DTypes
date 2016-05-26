\documentclass[preprint]{sigplanconf}

\usepackage[references]{agda} %% \AgdaRef{...}
\usepackage{datetime}
\usepackage[utf8x]{inputenc}
\usepackage{amsthm}
\usepackage{bbold}
\usepackage{url}
\usepackage{xcolor}
\usepackage{amssymb}
\usepackage{multicol}
\usepackage{proof}
\usepackage{amstext}
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{stmaryrd}
\usepackage{mathrsfs}
\usepackage{mathabx}
\usepackage{tikz}
\usepackage{tikz-cd}
\usetikzlibrary{quotes}

\newcommand{\amr}[1]{\fbox{\begin{minipage}{0.4\textwidth}\color{purple}{Amr says: #1}\end{minipage}}}

\newcommand{\pifrac}{\Pi^/}
\newcommand{\alt}{~|~}
\newcommand{\ag}[2]{#1 \sslash #2}
\newcommand{\order}[1]{\hash #1}
\newcommand{\inl}[1]{\textsf{inl}(#1)}
\newcommand{\inr}[1]{\textsf{inr}(#1)}
\newcommand{\zt}{\mathbb{0}}
\newcommand{\ot}{\mathbb{1}}
\newcommand{\G}{\mathcal{G}}
\newcommand{\Z}{\mathbb{Z}}
\newcommand{\Zn}{\mathbb{Z}_n}
\newcommand{\Zvn}{\mathbb{Z}^v_n}
\newcommand{\cycle}{\textsf{cycle}}
\newcommand{\twod}{\mathbb{T}}
\newcommand{\fract}[2]{#1/#2}
%% \newcommand{\mystrut}{\rule[-0.01\baselineskip]{0pt}{2.2\baselineskip}}
\newcommand{\fv}[2]{\fcolorbox{black}{white}{\strut $#1$}\fcolorbox{black}{gray!20}{$\strut #2$}}
\newcommand{\pt}[2]{\bullet[#1,#2]}
\newcommand{\refl}{\AgdaInductiveConstructor{refl}}

\theoremstyle{remark}
\newtheorem{definition}{Definition}
\newtheorem{example}{Example}

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

\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}
module popl where
open import pibackground
\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\conferenceinfo{CONF 'yy}{Month d--d, 20yy, City, ST, Country}
\copyrightyear{20yy}
\copyrightdata{978-1-nnnn-nnnn-n/yy/mm}
\copyrightdoi{nnnnnnn.nnnnnnn}

\titlebanner{Fractional Types and Negative Information}
\preprintfooter{\today\ \currenttime}

\title{Fractional Types and Negative Information} 
\authorinfo{Anonymous}{}{}
%% Chao-Hong Chen, Vikraman Choudhury, Robert Rose,
%% Jacques Carette, Amr Sabry
\maketitle

\begin{abstract}
\amr{todo}
\end{abstract}

%% \category{CR-number}{subcategory}{third-level}
%% \terms
%% term1, term2
%% \keywords
%% keyword1, keyword2

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction}

In Homotopy Type Theory (HoTT)~\citeyearpar{hottbook}, types are
\emph{weak $\omega$-groupoids}. As a first approximation, we can think
of such structures as sets with points (objects) and connections
(equivalences) between the points and connections between these
connections and so on. Here are two simple but non-trivial examples:

\medskip
\begin{figure}[h]
\begin{tabular}{c@{\qquad}c}
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
  \draw[dashed] (0,0) ellipse (1.5cm and 2.1cm);
  \node[below] (B) at (0,-0.7) {\texttt{*}};
  \path (B) edge [loop below] node[below] {\texttt{id}} (B);
  \path (B) edge [loop above, looseness=15, in=48, out=132] node[above] {$p$} (B);
  \path (B) edge [loop above, looseness=25, in=40, out=140] node[above] {$q$} (B);
\end{tikzpicture}
\end{tabular}
\caption{\label{fig:groupoids}(a) The groupoid $\ag{6}{3}$ \qquad (b) The groupoid $\frac{1}{3}$}
\end{figure}

\medskip\noindent \citet{groupoidcard} assign to each groupoid a
\emph{cardinality} that counts the objects up to equivalences. The
groupoid on the left has six points \texttt{a}, \texttt{b},
\texttt{c}, \texttt{d}, \texttt{e}, and \texttt{f} that are clustered
in two equivalence classes and hence the groupoid has
cardinality~2. The groupoid on the right has one point \texttt{*} with
three distinct equivalences \texttt{id}, $p$, and~$q$ on it and hence
has cardinality $\frac{1}{3}$.

Both groupoids illustrated in Fig.~\ref{fig:groupoids} involve some
notion of ``division'' that can be captured at the level of types
using a syntactic notion of \emph{fractional types.} The existence of
such fractional types that denote groupoids as the ones depicted in
Fig.~\ref{fig:groupoids} raises an intriguing question about their
applicability to programming practice. In this introduction, we
present, in the context of a new language $\pifrac$, several
inter-related motivations and applications of fractional types that
are formalized and justified in the remainder of the paper.

\paragraph*{Quotient Types.} Groupoids similar to $\ag{6}{3}$ in
Fig.~\ref{fig:groupoids}(a) intuitively correspond to conventional
\emph{quotient types}. Traditionally~\citep {quotient}, a quotient
type $\ag{T}{E}$ combines a type $T$ with an equivalence relation $E$
that serves as the equality relation on the elements of $T$. Our
notion of fractional types in $\pifrac$ will subsume conventional
quotient types and their applications~\citep{Cohen2013} (e.g.,
defining fractions, multivariate polynomials, field extensions,
algebraic numbers, etc.)

\paragraph*{First-class Equivalence Relations.} Groupoids similar to
$\frac{1}{3}$ in Fig.~\ref{fig:groupoids}(b) can be thought of as a
limiting case of quotient types $\ag{1}{3}$ which consist of purely an
equivalence relation. We therefore think of such groupoids as
representing a \emph{first-class} notion of equivalence relations. As
explained in the remainder of the paper, such relations are
represented using special programs $p$ in $\pifrac$ and the type
$\frac{1}{p}$ represents the equivalence relation generated by this
program. In other words, instead of just quotient types in which the
equivalence relation is hardwired, it is possible to use existing
$\pifrac$ programs to generate and manipulate equivalence relations as
first-class values independently of the types they eventually act
upon. These first-class equivalence relations therefore enhance $\pifrac$
with the same expressiveness afforded by the presence of first-class
functions in conventional languages.

\paragraph*{Conservation of Information and Negative Entropy.} A
finite type with $n$ elements where $n$ is a non-zero natural number
has entropy $\log{n}$. This entropy is a measure of information which
materializes itself in memory or bandwidth requirements when storing
or transmitting elements of this type. Thus a type with 8 elements
needs 3 bits of memory for storage or 3 bits of bandwidth for
communication. If quantum field theory is correct (as it so far seems
to be) then information, during any physical process, is neither
created nor
destroyed. Landauer~\citeyearpar{Landauer:1961,bennett1985fundamental,Landauer},
Bennet~\citeyearpar{Bennett:1973:LRC,bennett2003notes,bennett2010notes},
Fredkin~\citeyearpar{fredkin1982conservative} and others made
compelling arguments that this physical principle induces a
corresponding computational principle of ``conservation of
information.'' In the context of finite types, this means that the
foundational notion of computation is computation via type
isomorphisms~\cite{James:2012:IE:2103656.2103667} or HoTT
equivalences~\cite{Carette2016} which are both
cardinality-preserving. The introduction, in $\pifrac$, of types
(groupoids) with fractional cardinalities introduces types with
\emph{negative entropy}. For example, a type with cardinality
$\frac{1}{8}$ has negative entropy $\log{\frac{1}{8}} = -3$. In
the context of $\pifrac$ we will interpret this negative entropy just
like we interpret negative money, as a debt to be repaid by some other
part of the system. This ability to manipulate negative information as
a first-class entity enhances $\pifrac$ with an expressiveness similar
to the one afforded by the presence of negative numbers in finance.

\paragraph*{Resource Creation and Annihilation.} In $\pifrac$ all
programs preserve information and hence preserve
cardinality. Furthermore, for non-zero natural numbers $n$, the
cardinality of the type $n \times \frac{1}{n}$ in $\pifrac$
is~1. Therefore, $\pifrac$ has, for example, terms of type
$1 \rightarrow (8 \times \frac{1}{8})$. Such terms take the type $1$
with entropy $\log{1} = 0$ to the type $8 \times \frac{1}{8}$ with
entropy $\log{8} + (- \log{8}) = 3 - 3 = 0$. The entropy is globally
preserved as desired and expected. But interestingly, the term
introduces, locally, two types that have entropies of $3$ and $-3$
respectively. Each of these types can be further processed
independently and, as long as the entire system is
information-preserving, the net positive and negative entropies must
eventually cancel out by a use of a term of the reverse type
$(8 \times \frac{1}{8}) \rightarrow 1$. The simplest way to appreciate
the expressiveness afforded by such a mechanism is the following
credit card analogy. Think of the computation of type
$1 \rightarrow (8 \times \frac{1}{8})$ as creating, out of nothing, 3
dollars to be paid to the merchant instantly with a corresponding debt
that propagates through the system. As long as the entire financial
system is debt-preserving, the debt is guaranteed to propagate to the
appropriate bank account and must eventually be reconciled by the
original buyer. In more conventional computational terms, what has
happened is that the resources needed at one point in the computation
were created and consumed instantly without requiring a
synchronization with the part of the system holding the resources,
giving us a more asynchronous and decentralized model of computation.

\paragraph*{Outline.} The remainder of the paper is organized as
follows. \ldots


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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Examples}

We present two examples that illustrate the novelty of fractional
types in a programming context. The first example is of a denotational
flavor showing how to decompose types in components that could be
processed independently. The second example, of a more operational
flavor, formalizes the credit card analogy from the introduction as an
executable program.

%%%%%
\subsection{$\sqrt{n}$ Speedup}

Say we want to add 1 $\pmod{100}$ to numbers in the range
$[0..99]$. One approach is to represent the input type as a monolithic
type with 100 elements giving us a unary representation of the
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
  \draw[dashed] (0,0) ellipse (8cm and 1.6cm);
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

\noindent The first step is to write a program $p$ that represents a
permutation of $C$ of order 3. For example:
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
identity function. The definition of any $p$ representing a
permutation of order $\hash p$ will induce two groupoids of
cardinality $\order{p}$ and $1/\hash p$. In our case, we get:
\begin{itemize}
\item The first groupoid which we denote $\order{p}$ has (up to
  equivalence) three clusters of objects corresponding to each
  distinct iteration of $p$. (We omit the identity arrows in the
  figure.) It has cardinality $3$:
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
\item The second groupoid which we denote $1/\hash~p$ has one 
trivial object and a loop for each distinct iteration of $p$. (We
explicitly include the identity arrow to emphasize that there are
three distinct loops):
\begin{center}
\begin{tikzpicture}[scale=0.4,every node/.style={scale=0.4}]
  \draw[dashed] (0,0) ellipse (1.5cm and 2.1cm);
  \node[below] (B) at (0,-0.7) {\texttt{*}};
  \path (B) edge [loop below] node[below] {$p^0$} (B);
  \path (B) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (B);
  \path (B) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (B);
\end{tikzpicture}
\end{center}
\end{itemize}

It is a fact that, in $\pifrac$, the trivial one point groupoid has the
same cardinality as $\order{p} \times 1/\hash p$ for any $p$. Indeed
taking the product of $\order{p}$ and $1/\hash p$ produces the groupoid:

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
C &≃&  C \times 1 \\
&≃& C \times (\order{p} \times 1/\hash p) \\
&≃& (C \times 1/\hash p) \times \order{p} 
\end{array}\]
which decomposes $C$ into the product of $C \times 1/\hash p$ and
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
 
Generally speaking, the values of $\order{p}$ are $p^0=\mathit{id}$,
$p$, $p^2$, etc. The values of $1/\hash p$ are $[*,p^0]$, $[*,p]$,
$[*,p^2]$, etc. $\eta$ has a choice: it always chooses $p$ and
$[*,p]$. $\epsilon$ has to have a matched pair to give 1; otherwise it
backtracks.

\noindent Initial circuit:

\begin{center}
\begin{tikzpicture}[scale=0.7,every node/.style={scale=0.7}]
  \draw (0,0) -- (1,0) -- (1,2) -- (0,2) -- cycle;
  \path (-1.1,1) edge node[below] {$\order{\textsf{swap}}$} (0,1);
  \path (1,1.8) edge node[above] {1} (1.6,1.8);
  \path (1,0.2) edge node[below] {$\order{\textsf{swap}}$} (4,0.2);
  \draw (1.6,0.8) -- (2.6,0.8) -- (2.6,2.8) -- (1.6,2.8) -- cycle;
  \path (2.6,2.6) edge node[above] {$\order{\textsf{swap}}$} (6,2.6);
  \path (2.6,1) edge node[above] {$1/\hash\textsf{swap}$} (4,1);
  \draw (4,0) -- (5,0) -- (5,2) -- (4,2) -- cycle;
  \path (5,1) edge node[above] {1} (6,1);
  \draw (6,0.8) -- (7,0.8) -- (7,2.8) -- (6,2.8) -- cycle;
  \path (7,1.8) edge node[above] {$\order{\textsf{swap}}$} (8,1.8);
  \node at (0.5,1) {$\textsf{unit*}$};
  \node at (2.1,1.8) {$\eta$};
  \node at (4.5,1) {$\epsilon$};
  \node at (6.5,1.8) {$\textsf{unit*}$};
\end{tikzpicture}
\end{center}

There are two possible inputs id and swap. If the input is swap then
execution proceeds as follows:
\begin{verbatim}
swap -> 
((),swap) -> 
((swap,[*,swap]),swap) ->
(swap,([*,swap],swap)) ->
(swap,()) ->
swap
\end{verbatim}

If the input is id then execution proceeds as follows:

\begin{verbatim}
  swap^0
>> unit* >>
  ((),swap^0)
>> eta x id >>
  ((swap^1,[*,swap^1]),swap^0)
>> assoc >>
  (swap^1,([*,swap^1],swap^0)) 
>> id x epsilon >>
  (swap^1,([*,swap^1],swap^0)) 
<< assoc <<
  ((swap^1,[*,swap^1]),swap^0)
<< eta x id <<
  ((swap^2,[*,swap^2]),swap^0)
>> assoc >>
  ((swap^2,[*,swap^2]),swap^0)
>> id x epsilon >>
  (swap^2,())
>> unit* >>
  swap^2
\end{verbatim}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Sec 3

\input{pibackground.tex} 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Sec 4

\input{groupoid.tex}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Sec 5, 6, and 7
%% A new language with fractional types
%% its denotational semantics
%% its operational semantics
%% pragmatics

\input{pifrac.tex}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\bibliographystyle{abbrvnat}
\bibliography{cites}
\end{document}

%% This type is again informally-equivalent to $\ag{C}{p}$ as it has the
%% same cardinality.

% \begin{tabular}{ccc}
% \begin{minipage}{0.4\textwidth}
% \begin{tikzpicture}[scale=0.3,every node/.style={scale=0.3}]
%   \draw (0,0) ellipse (9cm and 6cm);
%   \node[below] (1) at (-6,0) {\texttt{sun}};
%    \node[below] (2) at (-4,0) {\texttt{mon}};
%   \node[below] (3) at (-2,0) {\texttt{tue}};
%   \node[below] (4) at (0,0) {\texttt{wed}};
%   \node[below] (5) at (2,0) {\texttt{thu}};
%   \node[below] (6) at (4,0) {\texttt{fri}};
%   \node[below] (7) at (6,0) {\texttt{sat}};
%   \draw[fill] (-6,0) circle [radius=0.05];
%   \draw[fill] (-4,0) circle [radius=0.05];
%   \draw[fill] (-2,0) circle [radius=0.05];
%   \draw[fill] (0,0) circle [radius=0.05];
%   \draw[fill] (2,0) circle [radius=0.05];
%   \draw[fill] (4,0) circle [radius=0.05];
%   \draw[fill] (6,0) circle [radius=0.05];

%   \path (1) edge [loop above] node[above] {$p^0$} (1);
%   \path (1) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (1);
%   \path (1) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (1);

%   \path (2) edge [loop above] node[above] {$p^0$} (2);
%   \path (2) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (2);
%   \path (2) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (2);

%   \path (3) edge [loop above] node[above] {$p^0$} (3);
%   \path (3) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (3);
%   \path (3) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (3);

%   \path (4) edge [loop above] node[above] {$p^0$} (4);
%   \path (4) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (4);
%   \path (4) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (4);

%   \path (5) edge [loop above] node[above] {$p^0$} (5);
%   \path (5) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (5);
%   \path (5) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (5);

%   \path (6) edge [loop above] node[above] {$p^0$} (6);
%   \path (6) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (6);
%   \path (6) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (6);

%   \path (7) edge [loop above] node[above] {$p^0$} (7);
%   \path (7) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (7);
%   \path (7) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (7);
% \end{tikzpicture}
% \end{minipage}
% & 
% $\times$
% & 
% \begin{minipage}{0.4\textwidth}
% \begin{tikzpicture}[scale=0.3,every node/.style={scale=0.3}]
%   \draw (0,0) ellipse (8cm and 1.6cm);
%   \node[below] at (-6,0) {\texttt{sun}};
%    \node[below] at (-4,0) {\texttt{mon}};
%   \node[below] at (-2,0) {\texttt{tue}};
%   \node[below] at (0,0) {\texttt{wed}};
%   \node[below] at (2,0) {\texttt{thu}};
%   \node[below] at (4,0) {\texttt{fri}};
%   \node[below] at (6,0) {\texttt{sat}};
%   \draw[fill] (-6,0) circle [radius=0.05];
%   \draw[fill] (-4,0) circle [radius=0.05];
%   \draw[fill] (-2,0) circle [radius=0.05];
%   \draw[fill] (0,0) circle [radius=0.05];
%   \draw[fill] (2,0) circle [radius=0.05];
%   \draw[fill] (4,0) circle [radius=0.05];
%   \draw[fill] (6,0) circle [radius=0.05];
%   \draw[->] (-6,0) -- (-4,0);
%   \draw[->] (-4,0) -- (-2,0);
%   \draw[->] (0,0) -- (2,0);
%   \draw[->] (2,0) -- (4,0);
%   \draw[->] (-6,0) to[bend left] (-2,0) ;
%   \draw[->] (0,0) to[bend left] (4,0) ;
% \end{tikzpicture}
% \end{minipage}
% \end{tabular}

% The type of the left is equivalent to a type with $2\frac{1}{3}$
% elements. The type of the right is equivalent to a type with 3
% elements. So we have divided our 7 elements into the product of
% $2\frac{1}{3}$ and 3 and we can operate on each cluster
% separately. After simplification, the situation reduces to:

% \medskip

% \begin{tabular}{ccc}
% \begin{minipage}{0.4\textwidth}
% \begin{tikzpicture}[scale=0.5,every node/.style={scale=0.5}]
%   \draw (0,0) ellipse (6cm and 4cm);
%   \node[below] (3) at (-3,0) {\texttt{smt}};
%   \node[below] (4) at (0,0) {\texttt{wrf}};
%   \node[below] (5) at (3,0) {\texttt{sat}};
%   \draw[fill] (-3,0) circle [radius=0.05];
%   \draw[fill] (0,0) circle [radius=0.05];
%   \draw[fill] (3,0) circle [radius=0.05];

%   \path (5) edge [loop above] node[above] {$p^0$} (5);
%   \path (5) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (5);
%   \path (5) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (5);
% \end{tikzpicture}
% \end{minipage}
% & 
% $\times$
% & 
% \begin{minipage}{0.4\textwidth}
% \begin{tikzpicture}[scale=0.5,every node/.style={scale=0.5}]
%   \draw (0,0) ellipse (5cm and 1.6cm);
%   \node[below] at (-3,0) {\texttt{smt}};
%   \node[below] at (0,0) {\texttt{wrf}};
%   \node[below] at (3,0) {\texttt{sat}};
%   \draw[fill] (-3,0) circle [radius=0.05];
%   \draw[fill] (0,0) circle [radius=0.05];
%   \draw[fill] (3,0) circle [radius=0.05];
% \end{tikzpicture}
% \end{minipage}
% \end{tabular}

% If we were to recombine the two types we would get:

% \medskip

% \begin{tikzpicture}[scale=0.5,every node/.style={scale=0.5}]
%   \draw (0,0) ellipse (12cm and 4cm);

%   \node[below] (1) at (-11,0) {\texttt{(smt,smt)}};
%   \node[below] (2) at (-8,0) {\texttt{(wrf,smt)}};
%   \node[below] (3) at (-5,0) {\texttt{(sat,smt)}};
%   \draw[fill] (-11,0) circle [radius=0.05];
%   \draw[fill] (-8,0) circle [radius=0.05];
%   \draw[fill] (-5,0) circle [radius=0.05];
%   \path (3) edge [loop above] node[above] {$p^0$} (3);
%   \path (3) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (3);
%   \path (3) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (3);

%   \node[below] (4) at (-3,0) {\texttt{(smt,wrf)}};
%   \node[below] (5) at (-1,0) {\texttt{(wrf,wrf)}};
%   \node[below] (6) at (1,0) {\texttt{(sat,wrf)}};
%   \draw[fill] (-3,0) circle [radius=0.05];
%   \draw[fill] (-1,0) circle [radius=0.05];
%   \draw[fill] (1,0) circle [radius=0.05];
%   \path (6) edge [loop above] node[above] {$p^0$} (6);
%   \path (6) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (6);
%   \path (6) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (6);

%   \node[below] (7) at (3,0) {\texttt{(smt,sat)}};
%   \node[below] (8) at (5,0) {\texttt{(sat,wrf)}};
%   \node[below] (9) at (7,0) {\texttt{(sat,sat)}};
%   \draw[fill] (3,0) circle [radius=0.05];
%   \draw[fill] (5,0) circle [radius=0.05];
%   \draw[fill] (7,0) circle [radius=0.05];
%   \path (9) edge [loop above] node[above] {$p^0$} (9);
%   \path (9) edge [loop above, looseness=15, in=48, out=132] node[above] {$p^1$} (9);
%   \path (9) edge [loop above, looseness=25, in=40, out=140] node[above] {$p^2$} (9);
% \end{tikzpicture}

% which is equivalent to $C$.

