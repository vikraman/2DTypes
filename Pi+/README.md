# README

This directory contains code attempting to prove the soundness and completeness of Π wrt to UFin, thus proving that the "+" fragment of Pi presents a univalent subuniverse.

## Code structure

The interesting content in the proof is the following chain of equivalences:
```agda
Pi combinators ≃ Lists of transpositions ≃ Lists of adjacent transpositions (Coxeter presentation of Sn) ≃ Lehmer n ≃ (Fin n ≃ Fin n)
```

The first two equivalences are unknown at the moment.

Code structure is as follows:
 - `Conjectures.agda` - general structure of the proof, proving that we have equivalences on 0-th level (Π types and UFin), 1-st level (Π 1-combinators and path space of UFin, which we'll prove is equivalent to Lehmer) and and 2-nd level (Π 2-combinators and 1-paths in Lehmer, which is a Prop). The main part of the proof happens on the 1-st level.
 - `Coxeter/` - contains the outline of the proof on 1-st level. This contains the outline of the third equivalence, i.e.
    ```agda
    List of adjacent transpositions (Coxeter presentation of Sn) ≃ Lehmer n
    ```
    The `Coxeter/README.md` explains that in detail.
 - `UFin.agda` - helper lemmas about UFin.
 - `Syntax.agda` - syntax of "+" fragment of Π.
 - `Level0.agda` - helper lemmas about 0-th level of Π.
 - `ShiftHIT.agda` - contains a definition of a HIT which is hypothesised to be equivalent to S_n - essentially, it's a presentation of S_n using shifts as generators and relations carried over from a Coxeter presentation. Maybe it will be useful later on.


## FSMG

`FSMG` contains two different descriptions of the free symmetric monoidal groupoid.
Using the above proof, we should be able to get the following corollary.

```
Ufin ≃ FSMG Unit
```

## Notes

Look into what sorting algorithm is actually ran as we compute with swap and assoc.
