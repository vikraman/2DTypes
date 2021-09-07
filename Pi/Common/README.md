# README - Common

This directory contains some general definitions and lemmas used thourought the proof.

## Code structure

  - `Arithmetic.agda` 
    - defines the ≤ order on ℕ (replicates the definition from Agda stdlib instead of using the one from HoTT stdlib for historic reasons)
    - defines the minus operation ∸
    - defines and states/proves a number of lemmas on interactions between + , ∸ and ≤
  - `InequalityEquiv.agda`
    - proves that the two definitions of orders on ℕ are equivalent
  - `ListN.agda`
    - defines the `Listℕ` type - ListN of natural numbers (we don't use the HoTT stdlib ListN because Agda has problems with decomposing them in pattern-matchings)
    - defines appending operator _++_
    - defines _↓_ which is the key part in the whole proof - n ↓ k represents a Listℕ [ (n + k) , (n + k - 1) , (n + k - 2) ... (n + 1) ]
    - proves a number of lemmas concering ListN, appends etc.
  - `LList.agda`
    - defines the `_>>_` type - an element of type `n >> l` for a natural number `n` and a ListN `l` proves that the
      list contains numbers less than `n` (essentially equivalent to `List (Fin n)`, but easier to work with in
      particular settings)
  - `ListFinLListEquiv.agda`
    - proves that `n >> l` is equivalent to the list containing elements of `Fin n`
  - `FinHelpers.agda`
    - some helpers for `Fin n` not found in the standard library
  - `Misc.agda`
    - helpers for HoTT equality
    - helpers for decidable equality
    - helpers for the equivalence relation
    - helpers for set quotients
    - helpers for group structure
  - `Extra.agda`
    - definitions for different kinds of `TODO`s used as placeholders for unproved holes
