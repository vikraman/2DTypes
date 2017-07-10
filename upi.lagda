\documentclass{entcs}
\usepackage{prentcsmacro}

\def\lastname{Carette, Chen, Choudhury, Rose, and Sabry}

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
\usepackage[conor,links,references]{agda}
\usepackage{stmaryrd}

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
  \address{Indiana University}
  \author{Vikraman Choudhury}
  \author{Robert Rose}
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

Copy.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{A Simple Reversible Programming Languages}

Copy.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Univalent Fibrations}
\label{sec:univalent}

\AgdaHide{
\begin{code}
  open import Agda.Primitive public using (Level ; lsuc ; lzero ; _⊔_)

  Type : (ℓ : Level) → Set (lsuc ℓ)
  Type ℓ = Set ℓ

  Type₀ = Type lzero
  Type₁ = Type (lsuc lzero)
\end{code}
}

We work in intensional type theory with one univalent universe closed
under propositional truncation.

\begin{code}
  data _==_ {ℓ} {A : Type ℓ} (a : A) : A → Type ℓ where
    refl : a == a
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Correspondence}
\label{sec:correspondence}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}
\label{sec:conclusion}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\bibliographystyle{acm}
{
  \footnotesize
  \bibliography{cites}
}

\end{document}
