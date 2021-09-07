# README - Coxeter

## Code structure

Listed here in dependency order.

Files introducing coxeter reduction relation:
  - `ImpossibleLists.agda`
    - Proves a number of lemmas showing that certain kinds of ListN are impossible (for example, that a Listℕ (n ↓ k) cannot have increasing sequence inside)
  - `ReductionRel.agda`
    - It introduces ≅ and its reflexive-transitive closure ≅*, which are acting on ListN of natural numbers
    - It proves a number of helper lemmas about the behaviour of it (for example, that it respects Listℕ concatenation)
    - Notice that the reduction relation decreases lexicographical order of its elements
  - `ExchangeLemmas.agda`
    - Deals with exchanging the order of single-element ListN and _↓_ ListN - shows under what condition are do we have (a ↓ b) ++ [c] ≅* [c] ++ (a ↓ b)

Diamond-related stuff:
  - `CritPairsLong.agda`
    - A Listℕ l contains critical pair, if it can be reduced in two different ways, i.e. there are two r1 r2 such that l ≅ r1 and l ≅ r2.
    - A pair can be resolved if there exists a common Listℕ r such that r1 ≅* r and r2 ≅* r
    - This file is the heart of the whole proof. It proves that each critical pair can be resolved. It does that by tediously checking every pair and finding appropriate reduction.
  - `Diamond.agda`
    - Collects all the critical pairs lemmas from the previous step and puts them together in the one big diamond lemma.
    - The termination checker is not happy, because we simply say "do the reduction as long as it's possible" (the same technique as in the standard proof in β-reduction of λ-calculus)
    - But the algorithm does terminate - the reduction relation always reduces lexicographical order, and it's a well-ordering of words, so eventually we get to normal form.
    - The proof has to be modified to make Agda happy.

Coxeter equivalence:
  - `MCoxeter.agda`
    - The definition of Modified Coxter relation - this is just the commutative closure of ReductionRel (the rules of ReductionRel are directed).
    - The end goal is to prove that this is equivalent to usual Coxeter presentation of S_n.
  - `MCoxterS.agda`
    - A helper relation, half-step between MCoxter and the real Coxter.
    - Probably could do without it, but I had some troubles with termination checker, so that's why I hacked it that way.
  - `Coxter.agda`
    - The definition of the standard Coxeter presentation of S_n
    - The proof that the MCoxter implies Coxter (`mcoxter->coxter`) is straigforward - after all, MCoxter rules are less powerful than their Coxter counterparts, because they are directed (`long` is more powerful than `braid`, but it can be very easily implemented in terms of `braid` and `swap`)
    - The other direction is more difficult - essentially, we want to prove that the if the relation is symmetric, then the generators of the relation can be made symmetric and the relation does not change. This requires `diamond`.

Lehmer equivalence:
  - `LehmerCanonical.agda`
    - Defines the Lehmer code and the operation `immersion` that turns a Lehmer code into a sequence of transpositions.
    - The first main result of this section is `final≅-Lehmer` - showing that immersions of Lehmer codes are normal forms wrt to ReductionRel (i.e. they can't be reduced any further).
    - A corollary of this is `only-one-canonical≃`, proving that if two immersions of Lehmer codes are related by ≃, then they are the same Lehmer codes 
    - This proves that `immersion` is an injection
  - `ReductionRel+.agda`
    - A helper module - normal `ReductionRel` is a (Kleene star) *-completion over ≅, and this is +-completion - one or more reductions. 
    - It's useful for defining that something is not a normal form - if it's not, then there exists n-step reduction (n > 1) to a normal form
  - `ExchangeLemmas+.agda`
    - The analogue of `ExchangeLemmas.agda`, but with a stronger conditions that the reductions should be at least 1-step long.
  - `LehmerReduction.agda`
    - Defines a `LehmerProper` type - an analogue to `Lehmer`, but it's now keeping just the non-empty indices. They can be converted from and back to normal Lehmer, but it's not an equivalence.
    - Proves that whether something is an immersion of `LehmerProper` is decidable.
    - Proves that everything reduces to an image of `LehmerProper` (this this is the canonical form).
    - Converts that proof to the proof that everything reduces to an image of `Lehmer`.
