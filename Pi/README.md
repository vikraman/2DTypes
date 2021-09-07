# README

This directory contains the formalisation of the denotational semantics of Pi, accompanying the paper. `Everything.agda`
is the main entrypoint to the project.

## Code structure

  - `Common`: Common lemmas and definitions about natural numbers and lists, used thorought the project.
  - `Coxeter`: Definition and properties of Coxete relation and the rewriting system based on it.
  - `Equiv`: The main proof of equivalence between Pi and UFin.
  - `Examples`: Examples of reversible boolean circuits showing applications of the semantics.
  - `Experiments`: Various experiments and earlier results.
  - `FSMG`: Free symmetric monoidal groupoids.
  - `Lehmer`: Lehmer codes.
  - `Syntax`: Syntax of Pi and its variants.
  - `UFin`: Construction of UFin and various properties.
  
## Checking the code

The formalisation has been checked using [Agda 2.6.1.3](https://hackage.haskell.org/package/Agda-2.6.1.3) and [HoTT-Agda
(Andrew Swan's fork)](https://github.com/awswan/HoTT-Agda/tree/agda-2.6.1-compatible).

To typecheck, run
```bash
make
```
in the main directory.

## Comments

  - In the formalisation, there is an additional step of going through Pi+ variant where types are indexed by their
    cardinality, this makes it easier to write some proofs which perform induction on the syntax, and eliminate some
    absurd cases.
  - Proving termination for certain functions is difficult in Agda, and we assert they're terminating. It is easy to see
    on paper that they terminate.
  - In HoTT-Agda, univalence/HITs are asserted as postulates, and they don't compute. The proofs rely on beta/eta
    reduction done "by hand", which is not explicitly done in the paper.
  - Using the formalised rewriting system to compute the normalisation function is very slow. We include several
    examples in the formalisation and it takes a while to compute them. Some computations are intractable, and we have
    left them commented out.
  - Translating commutative diagrams for large coherence results to Pi combinators is tedious. Similarly, using
    decidable equality and case matches to define large functions and reductions and then proving things about them is
    tedious. Some parts of the formalisation have been left as TODOs but we provide references for them, or show how to
    prove them on paper.
