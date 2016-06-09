%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Background}

The main syntactic vehicle for the technical developments in this paper is a
simple language called $\Pi$ whose only computations are isomorphisms between
finite types~\cite{James:2012:IE:2103656.2103667}. After reviewing the
motivation for this language and its relevance to HoTT, we present its syntax
and semantics.

\begin{figure*}[ht]
\[\begin{array}{cc}
\begin{array}{rrcll}
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
\end{array}
& 
\begin{minipage}{0.4\textwidth}
\[\begin{array}{c}
\Rule{}
{}
{\jdg{}{}{\idiso : \tau \iso \tau}}
{}
\\
\\
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
\\
\\
\Rule{}
{\jdg{}{}{c_1 : \tau_1 \iso \tau_2} \quad \vdash c_2 : \tau_3 \iso \tau_4}
{\jdg{}{}{c_1 \otimes c_2 : \tau_1 \otimes \tau_3 \iso \tau_2 \otimes \tau_4}}
{}
\end{array}\]
\end{minipage}
\end{array}\]
Each 1-combinator $c$ has an inverse $!~c$, e.g, $!~\unitepl=\unitipl$,
$!(c_1 \odot c_2) = ~!c_2 \odot~ !c_1$, etc.
\caption{$\Pi$-combinators~\cite{James:2012:IE:2103656.2103667}
\label{pi-combinators}}
\end{figure*}

\begin{figure*}[ht]
\[\begin{array}{c}
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
\quad
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
\quad
\Rule{}
{c : \tau_1 \iso \tau_2}
{\jdg{}{}{\linvdl : c ~\odot ~! c \isotwo \idiso : \linvdr}}
{}
\\
\\
\Rule{}
{c : \tau_1 \iso \tau_2}
{\jdg{}{}{\idisotwo : c \isotwo c}}
{}
\quad
\Rule{}
{c_1,c_2,c_3 : \tau_1 \iso \tau_2 \quad \alpha_1 : c_1 \isotwo c_2 \quad \alpha_2 : c_2 \isotwo c_3}
{\jdg{}{}{\transtwo ~\alpha_1 ~\alpha_2 : c_1 \isotwo c_3}}
{}
\\
\\
\Rule{}
{c_1,c_3 : \tau_1 \iso \tau_2 \quad c_2,c_4 : \tau_2 \iso \tau_3 \quad
  \alpha_1 : c_1 \isotwo c_3 \quad \alpha_2 : c_2 \isotwo c_4}
{\jdg{}{}{\alpha_1 \respstwo \alpha_2 : c_1 \odot c_2 \isotwo c_3 \odot c_4}}
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
$2!(\transtwo~\alpha_1~\alpha_2) = \transtwo~(2!~\alpha_2)~(2!~\alpha_1)$, etc. 

\caption{$\Pi$-combinators~\cite{James:2012:IE:2103656.2103667}
\label{pi-combinators2}}
\end{figure*}

\begin{figure*}[ht]
\begin{multicols}{2}
\[\begin{array}{r@{\!}lcl}
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
\evalone{\assocrp}{&(\inr{v})} &=& \inr{(\inr{v})} \\
\\
\evalone{\unitetl}{&(\unitv,v)} &=& v \\
\evalone{\unititl}{&v} &=& (\unitv,v) \\
\evalone{\unitetr}{&(v,\unitv)} &=& v \\
\evalone{\unititr}{&v} &=& (v,\unitv) \\
\evalone{\swapt}{&(v_1,v_2)} &=& (v_2,v_1) \\
\evalone{\assoclt}{&(v_1,(v_2,v_3))} &=& ((v_1,v_2),v_3) \\
\evalone{\assocrt}{&((v_1,v_2),v_3)} &=& (v_1,(v_2,v_3)) \\
\end{array}\]
\[\begin{array}{r@{\!}lcl}
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
\evalone{\factorl}{&\inr{(v_2,v_3)}} &=& (v_2,\inr{v_3}) \\
\\
\evalone{\idiso}{&v} &=& v \\
\evalone{(c_1 \odot c_2)}{&v} &=& 
  \evalone{c_2}{(\evalone{c_1}{v})} \\
\evalone{(c_1 \oplus c_2)}{&(\inl{v})} &=& 
  \inl{(\evalone{c_1}{v})} \\
\evalone{(c_1 \oplus c_2)}{&(\inr{v})} &=& 
  \inr{(\evalone{c_2}{v})} \\
\evalone{(c_1 \otimes c_2)}{&(v_1,v_2)} &=& 
  (\evalone{c_1}v_1, \evalone{c_2}v_2) 
\end{array}\]
\end{multicols}
\caption{\label{opsem}Operational Semantics}
\end{figure*}

%%%%%%%%%%%%%%%%%%%%%
\subsection{Reversibility} 

The relevance of reversibility to HoTT is based on the following
analysis. The conventional HoTT approach starts with two, a priori, different
notions: functions and paths, and then postulates an equivalence between a
particular class of functions and paths. As illustrated above, some functions
like \AgdaFunction{not} correspond to paths. Most functions, however, are
evidently unrelated to paths. In particular, any function of type
\AgdaBound{A}~\AgdaSymbol{→}~\AgdaBound{B} that does not have an inverse of
type \AgdaBound{B}~\AgdaSymbol{→}~\AgdaBound{A} cannot have any direct
correspondence to paths as all paths have inverses. An interesting question
then poses itself: since reversible computational models --- in which all
functions have inverses --- are known to be universal computational models,
what would happen if we considered a variant of HoTT based exclusively on
reversible functions?  Presumably in such a variant, all functions --- being
reversible --- would potentially correspond to paths and the distinction
between the two notions would vanish making the univalence postulate
unnecessary. This is the precise technical idea we investigate in detail in
the remainder of the paper.

%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Syntax of $\Pi$}
\label{opsempi}

The $\Pi$ family of languages is based on type isomorphisms. In the variant
we consider, the set of types $\tau$ includes the empty type $\zt$, the unit type
$\ot$, and conventional sum and product types. The values classified by these
types are the conventional ones: $\unitv$ of type $\ot$, $\inl{v}$ and $\inr{v}$ for
injections into sum types, and $(v_1,v_2)$ for product types:
\[\begin{array}{lrcl}
(\textrm{Types}) & 
  \tau &::=& \zt \alt \ot \alt \tau_1 \oplus \tau_2 \alt \tau_1 \otimes \tau_2 \\
(\textrm{Values}) & 
  v &::=& \unitv \alt \inl{v} \alt \inr{v} \alt (v_1,v_2) \\
(\textrm{1-combinators}) & 
  c &:& \tau_1 \iso \tau_2 ~ [\textit{see Fig.~\ref{pi-combinators}}] \\
(\textrm{2-combinators}) &
  \alpha &:& c_1 \isotwo c_2 \mbox{~where~} c_1, c_2 : \tau_1 \iso \tau_2 \\
  & && [\textit{see Fig.~\ref{pi-combinators2}}]
\end{array}\]
The interesting syntactic category of $\Pi$ is that of \emph{combinators}
which are witnesses for type isomorphisms $\tau_1 \iso \tau_2$. They consist
of base combinators (on the left side of Fig.~\ref{pi-combinators}) and
compositions (on the right side of the same figure). Each line of the figure
on the left introduces a pair of dual constants\footnote{where $\swapp$ and
$\swapt$ are self-dual.} that witness the type isomorphism in the
middle. This set of isomorphisms is known to be
complete~\cite{Fiore:2004,fiore-remarks} and the language is universal for
hardware combinational
circuits~\cite{James:2012:IE:2103656.2103667}.\footnote{If recursive types
and a trace operator are added, the language becomes Turing
complete~\cite{James:2012:IE:2103656.2103667,rc2011}. We will not be
concerned with this extension in the main body of this paper but it will be
briefly discussed in the conclusion.}

For $c_1, c_2 : \tau_1\iso\tau_2$, we have level-2 combinators $\alpha
: c_1 \isotwo c_2$ which are equivalences of isomorphisms, and which
happen to correspond to the coherence conditions for rig
groupoids. Many of the level 2 combinators not used. We only present
the ones we use in this paper.

\begin{proposition}
For any $c : \tau_1 \iso \tau_2$, we have $c \isotwo ~!~(!~c)$.
\end{proposition} 

\begin{proposition}
For any $c_1,c_2 : \tau_1 \iso \tau_2$, we have $c_1 \isotwo c_2$ implies
$!c_1 \isotwo ~!c_2$.
\end{proposition} 

%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Operational Semantics}

We give an operational semantics for $\Pi$.  Operationally, the
semantics consists of a pair of mutually recursive evaluators that
take a combinator and a value and propagate the value in the
``forward'' $\triangleright$ direction or in the
``backwards''~$\triangleleft$ direction. We show the complete forward
evaluator in Fig.~\ref{opsem}; the backwards evaluator differs in
trivial ways.

Every 1-combinator has an \emph{order} $n$: applying this combinator $n$ times is equivalent to the identity

A couple of examples: compute order

The type $(\ot \oplus \ot) \oplus \ot$ has cardinality 3 and hence has
6 automorphisms on it:

\[\begin{array}{rcl}
a_1 &=& \idiso \\
a_2 &=& \swapp \oplus \idiso \\
a_3 &=& \assocrp \odot (\idiso \oplus \swapp) \odot \assoclp \\
a_4 &=& a_2 \odot a_3 \\
a_5 &=& a_3 \odot a_2 \\
a_6 &=& a_4 \odot a_2
\end{array}\]

The combinators realize all the 3! permutations on the set of
cardinality 3. The permutation $a_1$ is the identity permutation; the
permutations $a_2$, $a_3$, and $a_6$ swap two of the three elements
leaving the third intact; the permutations $a_4$ and $a_5$ rotate the
three elements. A crucial property of combinators is their
\emph{order} which classifies them according to the number of
iterations needed for them to compose to the identity. In our case,
the reader is invited to check the following: $\mathit{order}(a_1)=1$,
$\mathit{order}(a_2)=\mathit{order}(a_3)=\mathit{order}(a_6)=2$, and
$\mathit{order}(a_4)=\mathit{order}(a_5)=3$. Generally speaking to
calculate the order of a combinator $c$, we apply $c$ to every value
and observe the length of the orbit. The order is the lcm of all the
orbits.

%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Groupoid Model} 

From the perspective of category theory, the language $\Pi$ models what is
called a \emph{symmetric bimonoidal category} or a \emph{commutative rig
category}. These are categories with two binary operations and satisfying the
axioms of a commutative rig (i.e., a commutative ring without negative
elements also known as a commutative semiring) up to coherent
isomorphisms. And indeed the types of the $\Pi$-combinators are precisely the
commutative semiring axioms. A formal way of saying this is that $\Pi$ is the
\emph{categorification}~\cite{math/9802029} of the natural numbers. A simple
(slightly degenerate) example of such categories is the category of finite
sets and permutations in which we interpret every $\Pi$-type as a finite set,
interpret the values as elements in these finite sets, and interpret the
combinators as permutations. 

Explain that we only reach a trivial class of groupoids

introduce discreteC and discreteG

Instead of modeling the types of $\Pi$ using sets and the combinators using
permutations we use a semantics that identifies $\Pi$-combinators with
\emph{paths}. More precisely, we model the universe of $\Pi$-types as a space
\AgdaFunction{U} whose points are the individual $\Pi$-types (which are
themselves spaces \AgdaBound{t} containing points). We then postulate that
there is path between the spaces \AgdaBound{t₁} and \AgdaBound{t₂} if there
is a $\Pi$-combinator $c : t_1 \iso t_2$. Our postulate is similar in spirit
to the univalence axiom but, unlike the latter, it has a simple computational
interpretation. A path directly corresponds to a type isomorphism with a
clear operational semantics as presented in the previous section. As we will
explain in more detail below, this approach replaces the datatype
\AgdaSymbol{≡} modeling propositional equality with the datatype
\AgdaSymbol{⟷} modeling type isomorphisms. With this switch, the
$\Pi$-combinators of Fig.~\ref{pi-combinators} become \emph{syntax} for the
paths in the space $U$. Put differently, instead of having exactly one
constructor \AgdaInductiveConstructor{refl} for paths with all other paths
discovered by proofs (see Secs. 2.5--2.12 of the HoTT
book~\citeyearpar{hottbook}) or postulated by the univalence axiom, we have
an \emph{inductive definition} that completely specifies all the paths in the
space $U$.

We begin with the datatype definition of the universe \AgdaFunction{U} of finite
types which are constructed using \AgdaInductiveConstructor{ZERO},
\AgdaInductiveConstructor{ONE}, \AgdaInductiveConstructor{PLUS}, and
\AgdaInductiveConstructor{TIMES}. Each of these finite types will correspond
to a set of points with paths connecting some of the points. The underlying
set of points is computed by \AgdaSymbol{⟦}\_\AgdaSymbol{⟧} as follows:
\AgdaInductiveConstructor{ZERO} maps to the empty set~\AgdaSymbol{⊥},
\AgdaInductiveConstructor{ONE} maps to the singleton set \AgdaSymbol{⊤},
\AgdaInductiveConstructor{PLUS} maps to the disjoint union \AgdaSymbol{⊎},
and \AgdaInductiveConstructor{TIMES} maps to the cartesian product
\AgdaSymbol{×}.

We note that the refinement of the $\Pi$-combinators to combinators on
pointed spaces is given by an inductive family for
\emph{heterogeneous} equality that generalizes the usual inductive
family for propositional equality. Put differently, what used to be
the only constructor for paths \AgdaInductiveConstructor{refl} is now
just one of the many constructors (named
\AgdaInductiveConstructor{id⟷} in the figure). Among the new
constructors we have \AgdaInductiveConstructor{◎} that constructs path
compositions. By construction, every combinator has an inverse
calculated as shown in Fig.~\ref{sym}. These constructions are
sufficient to guarantee that the universe~\AgdaFunction{U} is a
groupoid. Additionally, we have paths that connect values in different
but isomorphic spaces like \ldots

The example \AgdaFunction{notpath} which earlier required the use of the
univalence axiom can now be directly defined using
\AgdaInductiveConstructor{swap1₊} and \AgdaInductiveConstructor{swap2₊}. To
see this, note that \AgdaPrimitiveType{Bool} can be viewed as a shorthand for
\AgdaInductiveConstructor{PLUS} \AgdaInductiveConstructor{ONE}
\AgdaInductiveConstructor{ONE} with \AgdaInductiveConstructor{true} and
\AgdaInductiveConstructor{false} as shorthands for
\AgdaInductiveConstructor{inj₁} \AgdaInductiveConstructor{tt} and
\AgdaInductiveConstructor{inj₂} \AgdaInductiveConstructor{tt}. With this in
mind, the path corresponding to boolean negation consists of two ``fibers'',
one for each boolean value as shown below:

\noindent In other words, a path between spaces is really a collection of
paths connecting the various points. Note however that we never need to
``collect'' these paths using a universal quantification.

Shouldn't we also show that \AgdaPrimitiveType{Bool} contains exactly
$2$ things, and that TRUE and FALSE are ``different''? The other thing
is, whereas not used to be a path between Bool and Bool, we no longer
have that.  Shouldn't we show that, somehow, BOOL and BOOL.F 'union'
BOOL.T are somehow ``equivalent''?  And there there is a coherent
notpath built the same way?  Especially since I am sure it is quite
easy to build incoherent sets of paths!

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

