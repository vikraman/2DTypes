%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Programming with Equivalences}
\label{sec:pi}

The main syntactic vehicle for the technical developments
is the language $\Pi$ whose only computations are isomorphisms
between finite types and equivalences between these
isomorphisms~\cite{Carette2016,James:2012:IE:2103656.2103667}. We
present the syntax and operational semantics of the parts of the
language relevant to our work.

\begin{figure}[ht]
\[\begin{array}{rrcll}
\unitepl :&  \zt \oplus \tau & \iso & \tau &: \unitipl \\
\unitepr :&  \tau \oplus \zt & \iso & \tau &: \unitipr \\
\swapp :&  \tau_1 \oplus \tau_2 & \iso & \tau_2 \oplus \tau_1 &: \swapp \\
\assoclp :&  \tau_1 \oplus (\tau_2 \oplus \tau_3) & \iso & (\tau_1 \oplus \tau_2) \oplus \tau_3
  &: \assocrp \\
\\
\unitetl :&  \ot \otimes \tau & \iso & \tau &: \unititl \\
\unitetr :&  \tau \otimes \ot & \iso & \tau &: \unititr \\
\swapt :&  \tau_1 \otimes \tau_2 & \iso & \tau_2 \otimes \tau_1 &: \swapt \\
\assoclt :&  \tau_1 \otimes (\tau_2 \otimes \tau_3) & \iso & (\tau_1 \otimes \tau_2) \otimes \tau_3
  &: \assocrt \\
\\
\absorbr :&~ \zt \otimes \tau & \iso & \zt &: \factorzl \\
\absorbl :&~ \tau \otimes \zt & \iso & \zt &: \factorzr \\
\dist :&~ (\tau_1 \oplus \tau_2) \otimes \tau_3 &
  \iso & (\tau_1 \otimes \tau_3) \oplus (\tau_2 \otimes \tau_3)~ &: \factor \\
\distl :&~ \tau_1 \otimes (\tau_2 \oplus \tau_3) &
  \iso & (\tau_1 \otimes \tau_2) \oplus (\tau_1 \otimes \tau_3)~ &: \factorl
\end{array}\]

\[\begin{array}{c}
\Rule{}
{}
{\jdg{}{}{\idiso : \tau \iso \tau}}
{}
\qquad\qquad
\Rule{}
{\jdg{}{}{c_1 : \tau_1 \iso \tau_2} \quad \vdash c_2 : \tau_2 \iso \tau_3}
{\jdg{}{}{c_1 \odot c_2 : \tau_1 \iso \tau_3}}
{}
\\
\\
\Rule{}
{\jdg{}{}{c_1 : \tau_1 \iso \tau_2} \quad \vdash c_2 : \tau_3 \iso \tau_4}
{\jdg{}{}{c_1 \oplus c_2 : \tau_1 \oplus \tau_3 \iso \tau_2 \oplus \tau_4}}
{}
\qquad\qquad
\Rule{}
{\jdg{}{}{c_1 : \tau_1 \iso \tau_2} \quad \vdash c_2 : \tau_3 \iso \tau_4}
{\jdg{}{}{c_1 \otimes c_2 : \tau_1 \otimes \tau_3 \iso \tau_2 \otimes \tau_4}}
{}
\end{array}\]

Each 1-combinator $c$ has an inverse $!~c$, e.g, $!~\unitepl=\unitipl$,
$!(c_1 \odot c_2) = ~!c_2 \odot~ !c_1$, etc.
\caption{$\Pi$ 1-combinators~\cite{James:2012:IE:2103656.2103667}
\label{pi-combinators}}
\end{figure}

\begin{figure}[ht]
\[\begin{array}{c}
\Rule{}
{c : \tau_1 \iso \tau_2}
{\jdg{}{}{\idisotwo : c \isotwo c}}
{}
~
\Rule{}
{c_1,c_2,c_3 : \tau_1 \iso \tau_2 \quad \alpha_1 : c_1 \isotwo c_2 \quad \alpha_2 : c_2 \isotwo c_3}
{\jdg{}{}{\alpha_1~\transtwo~\alpha_2 : c_1 \isotwo c_3}}
{}
\\
\\
\Rule{}
{c_1 : \tau_1 \iso \tau_2 \quad c_2 : \tau_2 \iso \tau_3 \quad c_3 : \tau_3 \iso \tau_4}
{\jdg{}{}{\assocdl : c_1 \odot (c_2 \odot c_3) \isotwo (c_1 \odot c_2) \odot c_3 : \assocdr}}
{}
\\
\\
\Rule{}
{c : \tau_1 \iso \tau_2}
{\jdg{}{}{\idldl : \idiso \odot c \isotwo c : \idldr}}
{}
~
\Rule{}
{c : \tau_1 \iso \tau_2}
{\jdg{}{}{\idrdl : c \odot \idiso \isotwo c : \idrdr}}
{}
\\
\\
\Rule{}
{c : \tau_1 \iso \tau_2}
{\jdg{}{}{\rinvdl : ~! c \odot c \isotwo \idiso : \rinvdr}}
{}
~
\Rule{}
{c : \tau_1 \iso \tau_2}
{\jdg{}{}{\linvdl : c ~\odot ~! c \isotwo \idiso : \linvdr}}
{}
\\
\\
\Rule{}
{}
{\jdg{}{}{\sumid : \idiso\oplus\idiso \isotwo \idiso : \splitid}}
{}
\\
\\
\Rule{}
{c_1 : \tau_5\iso\tau_1 \quad c_2 : \tau_6\iso\tau_2 \quad c_3 :
    \tau_1\iso\tau_3 \quad c_4 : \tau_2\iso\tau_4}
{\jdg{}{}{\homps : (c_1\odot c_3)\oplus(c_2\odot c_4) \isotwo
    (c_1\oplus c_2) \odot (c_3\oplus c_4) : \homsp }}
{}
\\
\\
\Rule{}
{c_1,c_3 : \tau_1 \iso \tau_2 \quad c_2,c_4 : \tau_2 \iso \tau_3 \quad
  \alpha_1 : c_1 \isotwo c_3 \quad \alpha_2 : c_2 \isotwo c_4}
{\jdg{}{}{\alpha_1 ~\respstwo~ \alpha_2 : c_1 \odot c_2 \isotwo c_3 \odot c_4}}
{}
\\
\\
\Rule{}
{c_1,c_3 : \tau_1 \iso \tau_2 \quad c_2,c_4 : \tau_2 \iso \tau_3 \quad
  \alpha_1 : c_1 \isotwo c_3 \quad \alpha_2 : c_2 \isotwo c_4}
{\jdg{}{}{\respptwo ~\alpha_1 ~\alpha_2 : c_1 \oplus c_2 \isotwo c_3 \oplus c_4}}
{}
\\
\\
\Rule{}
{c_1,c_3 : \tau_1 \iso \tau_2 \quad c_2,c_4 : \tau_2 \iso \tau_3 \quad
  \alpha_1 : c_1 \isotwo c_3 \quad \alpha_2 : c_2 \isotwo c_4}
{\jdg{}{}{\respttwo ~\alpha_1 ~\alpha_2 : c_1 \otimes c_2 \isotwo c_3 \otimes c_4}}
{}
\end{array}\]
Each 2-combinator $\alpha$ has an inverse $2!~\alpha$, e.g, $2!~\assocdl=\assocdr$,
$2!(\alpha_1~\transtwo~\alpha_2) = (2!~\alpha_2)~\transtwo~(2!~\alpha_1)$, etc.
\caption{$\Pi$ 2-combinators (excerpt)~\cite{Carette2016}
\label{pi-combinators2}}
\end{figure}

\begin{figure}[ht]
{\footnotesize
\[\begin{array}{cc}
\begin{array}[t]{rlcl}
%% \evalone{\unitepl}{&(\inl{()})} \\
\evalone{\unitepl}{&(\inr{v})} &=& v \\
\evalone{\unitipl}{&v} &=& \inr{v} \\
\evalone{\unitepr}{&(\inl{v})} &=& v \\
%% \evalone{\unitepr}{&(\inr{()})} \\
\evalone{\unitipr}{&v} &=& \inl{v} \\
\evalone{\swapp}{&(\inl{v})} &=& \inr{v} \\
\evalone{\swapp}{&(\inr{v})} &=& \inl{v} \\
\evalone{\assoclp}{&(\inl{v})} &=& \inl{(\inl{v})} \\
\evalone{\assoclp}{&(\inr{(\inl{v})})} &=& \inl{(\inr{v})} \\
\evalone{\assoclp}{&(\inr{(\inr{v})})} &=& \inr{v} \\
\evalone{\assocrp}{&(\inl{(\inl{v})})} &=& \inl{v} \\
\evalone{\assocrp}{&(\inl{(\inr{v})})} &=& \inr{(\inl{v})} \\
\evalone{\assocrp}{&(\inr{v})} &=& \inr{(\inr{v})}
\end{array} &
\begin{array}[t]{rlcl}
\evalone{\unitetl}{&(\unitv,v)} &=& v \\
\evalone{\unititl}{&v} &=& (\unitv,v) \\
\evalone{\unitetr}{&(v,\unitv)} &=& v \\
\evalone{\unititr}{&v} &=& (v,\unitv) \\
\evalone{\swapt}{&(v_1,v_2)} &=& (v_2,v_1) \\
\evalone{\assoclt}{&(v_1,(v_2,v_3))} &=& ((v_1,v_2),v_3) \\
\evalone{\assocrt}{&((v_1,v_2),v_3)} &=& (v_1,(v_2,v_3))
\end{array} \\
\\
\begin{array}[t]{rlcl}
\evalone{\absorbr}{&(v,\_)} &=& v \\
\evalone{\absorbl}{&(\_,v)} &=& v \\
%% \evalone{\factorzl}{&()} \\
%% \evalone{\factorzr}{&()} \\
\evalone{\dist}{&(\inl{v_1},v_3)} &=& \inl{(v_1,v_3)} \\
\evalone{\dist}{&(\inr{v_2},v_3)} &=& \inr{(v_2,v_3)} \\
\evalone{\factor}{&\inl{(v_1,v_3)}} &=& (\inl{v_1},v_3) \\
\evalone{\factor}{&\inr{(v_2,v_3)}} &=& (\inr{v_2},v_3) \\
\evalone{\distl}{&(v_1,\inl{v_3})} &=& \inl{(v_1,v_3)} \\
\evalone{\distl}{&(v_2,\inr{v_3})} &=& \inr{(v_2,v_3)} \\
\evalone{\factorl}{&\inl{(v_1,v_3)}} &=& (v_1,\inl{v_3}) \\
\evalone{\factorl}{&\inr{(v_2,v_3)}} &=& (v_2,\inr{v_3})
\end{array} &
\begin{array}[t]{rlcl}
\evalone{\idiso}{&v} &=& v \\
\evalone{(c_1 \odot c_2)}{&v} &=&
  \evalone{c_2}{(\evalone{c_1}{v})} \\
\evalone{(c_1 \oplus c_2)}{&(\inl{v})} &=&
  \inl{(\evalone{c_1}{v})} \\
\evalone{(c_1 \oplus c_2)}{&(\inr{v})} &=&
  \inr{(\evalone{c_2}{v})} \\
\evalone{(c_1 \otimes c_2)}{&(v_1,v_2)} &=&
  (\evalone{c_1}v_1, \evalone{c_2}v_2)
\end{array}
\end{array}\]
\caption{\label{opsem}$\Pi$ operational semantics}
}
\end{figure}

%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Syntax of $\Pi$}
\label{opsempi}

The $\Pi$ family of languages is based on type isomorphisms. In the
variant we consider, the set of types $\tau$ includes the empty
type~$\zt$, the unit type $\ot$, and sum $\oplus$ and product
$\otimes$ types. The values classified by these types are the
conventional ones: $\unitv$ of type~$\ot$, $\inl{v}$ and $\inr{v}$ for
injections into sum types, and $(v_1,v_2)$ for product types. The
language has two other syntactic categories of programs to be
described in detail:
\[\begin{array}{lrcl}
(\textrm{Types}) &
  \tau &::=& \zt \alt \ot \alt \tau_1 \oplus \tau_2 \alt \tau_1 \otimes \tau_2 \\
(\textrm{Values}) &
  v &::=& \unitv \alt \inl{v} \alt \inr{v} \alt (v_1,v_2) \\
(\textrm{1-combinators}) &
  c &:& \tau_1 \iso \tau_2 ~ [\textit{see Fig.~\ref{pi-combinators}}] \\
(\textrm{2-combinators}) &
  \alpha &:& c_1 \isotwo c_2 \mbox{~where~} c_1, c_2 : \tau_1 \iso \tau_2
  ~[\textit{see Fig.~\ref{pi-combinators2}}]
\end{array}\]

\noindent Both classes of programs, 1-combinators $c$, and
2-combinators~$\alpha$, denote \emph{equivalences} in the HoTT sense. The
elements $c$ of 1-combinators denote type isomorphisms. The elements $\alpha$ of
2-combinators denote the set of sound and complete equivalences between these
type isomorphisms. Using the 1-combinators, it is possible to write any
reversible boolean function and hence encode arbitrary boolean functions by a
technique that goes back to Toffoli~\cite{Toffoli:1980}. The 2-combinators
provide a layer of programs that computes semantics-preserving transformations
of 1-combinators. As a small example, let us abbreviate $\ot \oplus \ot$ as the
type $\mathbb{2}$ of booleans and examine two possible implementations of
boolean negation. The first directly uses the primitive combinator
$\swapp : \tau_1 \oplus \tau_2 \iso \tau_2 \oplus \tau_1$ to exchange the two
values of type $\mathbb{2}$; the second use three consecutive uses of $\swapp$
to achieve the same effect:
\[\begin{array}{rcl}
\mathsf{not_1} &=& \swapp \\
\mathsf{not_2} &=& (\swapp \odot \swapp) \odot \swapp
\end{array}\]
We can write a 2-combinator whose \emph{type} is $\mathsf{not_2}
\isotwo \mathsf{not_1}$:
\[
(\linvdl ~\respstwo~ \idisotwo)~\transtwo~\idldl
\]
which not only shows the equivalence of the two implementations of negation but
also shows \emph{how} to transform one to the other. In this example, we focus
on the first two occurrences of $\swapp$ and use $\linvdl$ to reduce them to
$\idiso$ since they are inverses. We then use $\idldl$ to simplify the
composition of $\idiso$ with $\swapp$ to just $\swapp$.

Fig.~\ref{pi-combinators} lists all the 1-combinators which consist of
base combinators (top) and compositions (bottom). Each
line of the base combinators introduces a pair of dual
constants\footnote{where $\swapp$ and $\swapt$ are self-dual.} that
witness the type isomorphism in the middle. This set of isomorphisms
is known to be sound and
complete~\cite{Fiore:2004,fiore-remarks}. Fig.~\ref{pi-combinators2}
lists a few of the 2-combinators that we use in this paper. Each
2-combinator relates two 1-combinators of the same type and witnesses
their equivalence. Both 1-combinators and 2-combinators are invertible
and the 2-combinators behave as expected with respect to inverses of
1-combinators.  As the full set of 2-combinators has $113$ entries, we
only show a few of them here.

\begin{proposition}
For any $c : \tau_1 \iso \tau_2$, we have $c \isotwo ~!~(!~c)$.
\end{proposition}

\begin{proposition}
For any $c_1,c_2 : \tau_1 \iso \tau_2$, we have $c_1 \isotwo c_2$ implies
$!~c_1 \isotwo ~!~c_2$.
\end{proposition}

%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Semantics}
\label{sec:pisem}

We give an operational semantics for the 1-combinators of $\Pi$ which
represent the conventional layer of programs.  Operationally, the
semantics consists of a pair of evaluators that
take a combinator and a value and propagate the value in the forward
direction~$\triangleright$ or in the backward
direction~$\triangleleft$. We show the complete forward evaluator in
Fig.~\ref{opsem}; the backward evaluator is easy to infer.

\noindent\jc{To me, the most perspicuous representation of $\mathbb{3}$ is as a
\textbf{left-leaning tree}.  The elements of $\mathbb{3}$ are then names
of paths from the root to the leaves.  We can then abbreviate these names by
associating names to the leaves.  The action of permutations is then easy to
picture: it leaves the shape of the tree invariant -- which is quite important
as (1+1)+1 is isomorphism but not equal to 1+(1+1) -- and permutes the labels.
Which is also exactly what the code below does: it permutes the names of paths
from the root to the leaves.  But this allows one to illustrate the action
of $\permtwo$ as
\begin{tikzpicture}[level distance=0.5cm]
  \node {$\cdot$}
    child {node {$\cdot$}
      child {node {a}}
      child {node {b}}
    }
    child {node {c}} ;
\end{tikzpicture}
going to
\begin{tikzpicture}[level distance=0.5cm]
  \node {$\cdot$}
    child {node {$\cdot$}
      child {node {b}}
      child {node {a}}
    }
    child {node {c}} ;
\end{tikzpicture}
}

As an example, let $\mathbb{3}$ abbreviate the type
$(\ot \oplus \ot) \oplus \ot$. There are three values of type $\mathbb{3}$ which
are $ll=\inl{\inl{\unitv}}$, $lr=\inl{\inr{\unitv}}$, and
$r=\inr{\unitv}$. There are, up to equivalence, six combinators of type
$\mathbb{3} \iso \mathbb{3}$, each representing a different permutation of three
elements, which could be written as follows:
\[\begin{array}{rcl}
\permone &=& \idiso \\
\permtwo &=& \swapp \oplus \idiso \\
\permthree &=& \assocrp \odot (\idiso \oplus \swapp) \odot \assoclp \\
\permfour &=& \permtwo \odot \permthree \\
\permfive &=& \permthree \odot \permtwo \\
\permsix &=& \permfour \odot \permtwo
\end{array}\]
Tracing the evaluation of $\permtwo$ on each of the possible inputs yields:
\[\begin{array}{rcl}
\evalone{(\swapp\oplus\idiso)}{\inl{\inl{\unitv}}} &=& \inl{\evalone{\swapp}{\inl{\unitv}}} \\
&=& \inl{\inr{\unitv}} \\
\\
\evalone{(\swapp\oplus\idiso)}{\inl{\inr{\unitv}}} &=& \inl{\evalone{\swapp}{\inr{\unitv}}} \\
&=& \inl{\inl{\unitv}} \\
\\
\evalone{(\swapp\oplus\idiso)}{\inr{\unitv}} &=& \inr{\evalone{\idiso}{\unitv}} \\
&=& \inr{\unitv}
\end{array}\]
Thus the effect of combinator $\permtwo$ is to swap the values
$\inl{\inl{\unitv}}$ and $\inl{\inr{\unitv}}$ leaving the value
$\inr{\unitv}$ intact. Iterating $\permtwo$ again is therefore equivalent
to the identity permutation, which can be verified using the
2-combinators:
\[\begin{array}{rcl}
\permtwo \odot \permtwo &=& (\swapp \oplus \idiso) \odot (\swapp \oplus \idiso) \\
&\isotwo& (\swapp \odot \swapp) \oplus (\idiso \odot \idiso) \\
&\isotwo& \idiso \oplus \idiso \\
&=& \idiso
\end{array}\]
\jc{should we annotate the above with the names of the 2-combinators that perform
these?}

More generally we can iterate 1-combinators to produce different
reversible functions between finite sets, eventually wrapping around
at some number which represents the \emph{order} of the underlying
permutation.

\begin{definition}[Power of a 1-combinator]
  The $k^{th}$ power of a 1-combinator $p : \tau \iso \tau$, for
  $k \in \Z$ is
  \[
    p^k =
  \begin{cases}
    \idiso & k = 0 \\
    p \odot p^{k - 1} & k > 0 \\
    (!~p) \odot p^{k + 1} & k < 0 \\
  \end{cases}
  \]
\end{definition}

\begin{definition}[Order of a 1-combinator]
\label{def:order}
  The order of a 1-combinator $p : \tau \iso \tau$, $\ord{p}$, is the
  least postitive natural number $k \in \N^+$ such that
  $p^k \isotwo \idiso$.
\end{definition}

For our example combinators on the type $\mathbb{3}$, simple traces using the
operational semantics show the combinator $\permone$ is the identity
permutation; the combinators $\permthree$ and $\permsix$ swap two of the three
elements leaving the third intact; and the combinators $\permfour$ and
$\permfive$ rotate the three elements. We therefore have
$\mathit{order}(\permone)=1$,
$\mathit{order}(\permtwo)=\mathit{order}(\permthree)=\mathit{order}(\permsix)=2$,
and $\mathit{order}(\permfour)=\mathit{order}(\permfive)=3$.

% \begin{lemma}
%   Every $p : \tau \iso \tau$ has an order.
% \end{lemma}

% \begin{proof}
%   By cases.
%   \begin{enumerate}
%   \item $\ord{\idiso} = 1$
%   \item $\ord{\swapp} = \ord{\swapt} = 2$
%   \item $\ord{p_1 \odot p_2} = ???$
%   \item $\ord{p_1 \oplus p_2} = \ord{p_1 \otimes p_2} = \mathsf{lcm}(\ord{p_1}, \ord{p_2})$
%   \end{enumerate}
% \end{proof}

The 2-combinators, being complete equivalences between
1-combinators~\cite{Carette2016}, also capture equivalences regarding
power of combinators and their order.

% \begin{proof}
%   Trivial.
% \end{proof}

\noindent\jc{I believe these lemmas, but we don't actually have proofs
for them in our code.  We've been seriously bit by that before, where we
made mistakes in the statement of ``obvious'' results.  I don't think we
should put in any formal-looking result in the paper without a having a
proof.}
\begin{lemma}
\label{lem:distiterplus}
  For $p : \tau\iso\tau$, $m,n\in\Z$, we have a 2-combinator
  $\distiterplus{p}{m}{n} : (p^m \odot p^n) \isotwo p ^{m + n}$.
\end{lemma}

\begin{lemma}
\label{lem:ordertwo}
  For $p : \tau \iso \tau$, $n \in \Z$, $p^{k + n} \isotwo p^n$ where
  $k = \ord{p}$.
\end{lemma}

\paragraph*{Intermezzo.} For an information-theoretic perspective on
the language $\Pi$, we think of a type containing $N$ values as an
abstract system that has~$N$ distinguishable states. According to the
conventional theory of information~\cite{Shannon1948}, the amount of
information contained in each state of a system with $N$
distinguishable states is $(\log N)$ bits of information. For example,
the type $\mathbb{2}$ can be thought of as an abstract system with
two distinguishable states labeled $\mathsf{true}$ and
$\mathsf{false}$ each containing $\log 2 = 1$ bit. Similarly, the type
$\mathbb{3}$ can be thought of as an abstract system with three
distinguishable states each containing $\log 3$ bits. The logarithmic
map implies that information contained in a composite state is the sum
of the information contained in its constituents. For example, the
type $\mathbb{2} \otimes \mathbb{3}$ can be thought of a composite
system consisting of two independent unrelated subsystems. Each state
of the composite system therefore contains
$\log (2 * 3) = \log 2 + \log 3$ bits which is the sum of the
information contained in each subsystem. Since all the combinators
preserve cardinality, they are also information-preserving.

%%%%%
\subsection{Agda Formalization}

\jc{This feels like this serves no purpuse to the text.  Perhaps this
part of the Agda could be relegated to an appendix?  If it is crucial to the
story, then this shouldn't just be ``parked'' here, but explained.}
For future we show the Agda version of the main definitions and signatures of
the concepts introduced in this section.

\AgdaHide{\begin{code}
infix 50 _⊕_
infix 60 _⊗_
-- infix 60 _//_
-- infix 60 _\\_
infix  30 _⟷_
infix  30 _⇔_
infixr 50 _◎_
-- infixr 70 _⊡_
infixr 60 _●_
\end{code}}

\begin{code}
data U : Set where
  𝟘    : U
  𝟙    : U
  _⊕_  : U → U → U
  _⊗_  : U → U → U

-- 1-combinators

data Prim⟷ : U → U → Set where
  id⟷ :  {t : U} → Prim⟷ t t
  -- rest elided

data _⟷_ : U → U → Set where
  Prim : {t₁ t₂ : U} → (Prim⟷ t₁ t₂) → (t₁ ⟷ t₂)
  _◎_ :  {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  -- rest elided

! : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
! = {!!} -- definition elided

-- 2-combinators

data _⇔_ : {t₁ t₂ : U} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
  id⇔ : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} → c ⇔ c
  _●_  : ∀ {t₁ t₂} {c₁ c₂ c₃ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  idl◎r : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} → c ⇔ (Prim id⟷ ◎ c)
  idr◎l : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} → (c ◎ Prim id⟷) ⇔ c
  idr◎r   : ∀ {t₁ t₂} {c : t₁ ⟷ t₂} → c ⇔ (c ◎ Prim id⟷)
  -- rest elided

2! : {t₁ t₂ : U} {c₁ c₂ : t₁ ⟷ t₂} → (c₁ ⇔ c₂) → (c₂ ⇔ c₁)
2! = {!!} -- definition elided
\end{code}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
