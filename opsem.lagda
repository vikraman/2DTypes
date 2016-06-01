\AgdaHide{
\begin{code}
{-# OPTIONS --without-K #-}

module opsem where

\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Operational Semantics} 

First the equivalence can only make sense in a framework where
everything is reversible. If we allow arbitrary functions then bad
things happen as we can throw away the negative information for
example. In our reversible information-preserving framework, the
theory is consistent in the sense that not all types are
identified. This is easy to see as we only identify types that have
the same cardinality. This is evident for all the combinators except
for the new ones. For those new ones the only subtle situation is with
the empty type. Note however that there is no way to define 1/0 and no
permutation has order 0. For 0 we have one permutation id which has
order 1. So if we try to use it, we will map 1 to 1 times 1/id which
is fine. So if we always preserve types and trivially 1 and 0 have
different cardinalities so there is no way to identify them and we are
consistent.

"apply this program i times" is a VALUE !!!
  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

