%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Limitations}

Given any non-negative rational number, we can form a type whose cardinality is
that number. And yet, our types do not capture the full structure of the
non-negative rational numbers, as these form a commutative semifield. There are
a number of operations and properties which need to be added to complete this.
Most seem quite straightforward.  We can however single one out which may not
be: what we are missing is a multiplicative inverse for every type, and not just
$\order{p}$. In particular, we would like to form the type
$\iorder{(\iorder{p})}$ and have it be equivalent to $\order{p}$.  The
relationship between $\order{p}$ and $\iorder{p}$ in $\Pi^/$ reveals a pattern
that can be exploited to achieve this generalization. The multiplicative inverse
of $\order{p}$ is obtained by promoting the objects in $\order{p}$ to morphisms
in $1/\hash p$, which is a general process called \emph{delooping}. It is clear
we can go in the inverse direction by demoting morphisms to objects which is a
process called \emph{looping}. We leave a possible extension with a general
looping/delooping process to future work.

% The problem is that we cannot do this compositionally: say we have
% $\order{p_1}$ and $\order{p_2}$ and we deloop each to get $1/\hash p_1$ and
% $1/\hash p_2$ or cardinalities $\frac{1}{\order{p_1}}$ and
% $\frac{1}{\order{p_2}}$ respectively. Now say we construct $\order{p_1}
% \boxplus \order{p_2}$, we want the delooping to construct a space with
% cardinality $\frac{1}{\order{p_1}+\order{p_2}}$ but that has nothing to do
% with the individual deloopings.

A second more immediate concern is to discover the abstract monadic and/or
comonadic structure underlying the operational semantics. It is clear that the
operational interpretation of fractional types involves a computational effect
that requires synchronization with the ``future''. Implementing this effect
using backtracking, reference cells, or dataflow constraints is possible but
each implementation choice is ad hoc. We conjecture that with the right monadic
and/or comonadic abstraction, the operational semantics will be simpler and
expose still richer properties.  We chose the dependently-typed dataflow
semantics because we are able to prove that it is reversible and coherent,
unlike our previous attempts with explicit effects, none of which were provably
reversible and/or coherent.

%% not reversible; no inverses for all types; limited to 2-groupoids
