# README - Coxeter

## Code structure

First, files lowest in dependency order: these contain very general lemmas about behaviour of ℕ and lists.
  - `Arithmetic.agda` 
    - defines the ≤ order on ℕ (replicates the definition from Agda stdlib instead of using the one from HoTT stdlib for historic reasons)
    - defines the minus operation ∸
    - defines and states/proves a number of lemmas on interactions between + , ∸ and ≤
  - `Lists.agda`
    - defines the List type - lists of natural numbers (we don't use the HoTT stdlib lists because Agda has problems with decomposing them in pattern-matchings)
    - defines appending operator _++_
    - defines _↓_ which is the key part in the whole proof - n ↓ k represents a list [ (n + k) , (n + k - 1) , (n + k - 2) ... (n + 1) ]
    - proves a number of lemmas concering lists, appends etc
  - `ImpossibleLists.agda`
    - Proves a number of lemmas showing that certain kinds of lists are impossible (for example, that a list (n ↓ k) cannot have increasing sequence inside)

Files introducing coxeter reduction relation:
  - `ReductionRel.agda`
    - It introduces ≅ and its reflexive-transitive closure ≅*, which are acting on lists of natural numbers
    - It proves a number of helper lemmas about the behaviour of it (for example, that it respects list concatenation)
    - Notice that the reduction relation decreases lexicographical order of its elements
  - `ExchangeLemmas.agda`
    - Deals with exchanging the order of single-element lists and _↓_ lists - shows under what condition are do we have (a ↓ b) ++ [c] ≅* [c] ++ (a ↓ b)

Diamond-related stuff:
  - `CritPairsLong.agda`
    - A list l contains critical pair, if it can be reduced in two different ways, i.e. there are two r1 r2 such that l ≅ r1 and l ≅ r2.
    - A pair can be resolved if there exists a common list r such that r1 ≅* r and r2 ≅* r
    - This file is the heart of the whole proof. It proves that each critical pair can be resolved. It does that by tediously checking every pair and finding appropriate reduction.
  - `Diamond.agda`
    - Collects all the critical pairs lemmas from the previous step and puts them together in the one big diamond lemma.
    - The termination checker is not happy, because we simply say "do the reduction as long as it's possible" (the same technique as in the standard proof in β-reduction of λ-calculus)
    - But the algorithm does terminate - the reduction relation always reduces lexicographical order, and it's a well-ordering of words, so eventually we get to normal form.
    - The proof has to be modified to make Agda happy.
