\section{Appendix: Judgments}

\newenvironment{bprooftree}
{\leavevmode\hbox\bgroup}
{\DisplayProof\egroup}

\newcommand{\typ}{\texttt{ type}}
\newcommand{\injl}[1]{\ensuremath{\texttt{inj}_l({#1})}}
\newcommand{\injr}[1]{\ensuremath{\texttt{inj}_r({#1})}}

Type formation, equality and introduction rules, but no elimination forms.

\subsubsection*{Judgmental equality}

\[
  \begin{bprooftree}
    \AxiomC{$A \typ$}
    \UnaryInfC{$A = A$}
  \end{bprooftree}
\]

\subsubsection*{Base types}

\[
  \begin{bprooftree}
    \AxiomC{}
    \UnaryInfC{$\mathbb{0} \typ$}
  \end{bprooftree}
  \quad
  \begin{bprooftree}
    \AxiomC{}
    \UnaryInfC{$\mathbb{1} \typ$}
  \end{bprooftree}
  \quad
  \begin{bprooftree}
    \AxiomC{}
    \UnaryInfC{$\bullet \in \mathbb{1}$}
  \end{bprooftree}
\]

\subsubsection*{Sum and Product types}

\[
  \begin{bprooftree}
    \AxiomC{$A, B \typ$}
    \UnaryInfC{$A \oplus B \typ$}
  \end{bprooftree}
  \quad
  \begin{bprooftree}
    \AxiomC{$A = C$}
    \AxiomC{$B = D$}
    \BinaryInfC{$A \oplus B = C \oplus D$}
  \end{bprooftree}
\]

\[
  \begin{bprooftree}
    \AxiomC{$A, B \typ$}
    \AxiomC{$a \in A$}
    \BinaryInfC{$\injl{a} \in A \oplus B$}
  \end{bprooftree}
  \begin{bprooftree}
    \AxiomC{$A, B \typ$}
    \AxiomC{$b \in B$}
    \BinaryInfC{$\injr{b} \in A \oplus B$}
  \end{bprooftree}
\]

\[
  \begin{bprooftree}
    \AxiomC{$A, B \typ$}
    \UnaryInfC{$A \otimes B \typ$}
  \end{bprooftree}
  \quad
  \begin{bprooftree}
    \AxiomC{$A = C$}
    \AxiomC{$B = D$}
    \BinaryInfC{$A \otimes B = C \otimes D$}
  \end{bprooftree}
\]

\[
  \begin{bprooftree}
    \AxiomC{$A, B \typ$}
    \AxiomC{$a \in A$}
    \AxiomC{$b \in B$}
    \TrinaryInfC{$(a, b) \in A \otimes B$}
  \end{bprooftree}
\]

\subsubsection*{Level 1 combinators}

\[
  \begin{bprooftree}
    \AxiomC{$A, B \typ$}
    \UnaryInfC{$A \leftrightarrow B \typ$}
  \end{bprooftree}
  \quad
  \begin{bprooftree}
    \AxiomC{$A = C$}
    \AxiomC{$B = D$}
    \BinaryInfC{$A \leftrightarrow B = C \leftrightarrow D$}
  \end{bprooftree}
\]

\[
  \begin{bprooftree}
    \AxiomC{$A \typ$}
    \UnaryInfC{$\texttt{unite}_{+}l \in \mathbb{0} \oplus A \leftrightarrow A$}
  \end{bprooftree}
  \quad
  \begin{bprooftree}
    \AxiomC{$A \typ$}
    \UnaryInfC{$\texttt{unite}_{+}r \in A \leftrightarrow \mathbb{0} \oplus A$}
  \end{bprooftree}
\]

\[
  \begin{bprooftree}
    \AxiomC{$A \typ$}
    \UnaryInfC{$\texttt{id}\leftrightarrow \in A \leftrightarrow A$}
  \end{bprooftree}
  \quad
  \begin{bprooftree}
    \AxiomC{$A, B, C \typ$}
    \AxiomC{$p \in A \leftrightarrow B$}
    \AxiomC{$q \in B \leftrightarrow C$}
    \TrinaryInfC{$p \circledcirc q \in A \leftrightarrow C$}
  \end{bprooftree}
\]

\subsubsection*{Level 2 combinators}

\[
  \begin{bprooftree}
    \AxiomC{$A, B \typ$}
    \AxiomC{$p, q \in A \leftrightarrow B$}
    \BinaryInfC{$p \Leftrightarrow q \typ$}
  \end{bprooftree}
\]

\subsubsection*{Fractional types}

\[
  \begin{bprooftree}
    \AxiomC{$A \typ$}
    \AxiomC{$p \in A \leftrightarrow A$}
    \BinaryInfC{$\#p \typ$}
  \end{bprooftree}
\]
\[
  \begin{bprooftree}
    \AxiomC{$A \typ$}
    \AxiomC{$p, q \in A \leftrightarrow A$}
    \AxiomC{$r \in p \Leftrightarrow q$}
    \TrinaryInfC{$\#p = \#q$}
  \end{bprooftree}
\]

\[
  \begin{bprooftree}
    \AxiomC{$A \typ$}
    \AxiomC{$p \in A \leftrightarrow A$}
    \BinaryInfC{$1/\#p \typ$}
  \end{bprooftree}
\]
\[
  \begin{bprooftree}
    \AxiomC{$A \typ$}
    \AxiomC{$p, q \in A \leftrightarrow A$}
    \AxiomC{$r \in p \Leftrightarrow q$}
    \TrinaryInfC{$1/\#p = \mathbb{1}/\#q$}
  \end{bprooftree}
\]
