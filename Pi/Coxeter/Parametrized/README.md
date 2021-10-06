# README - Coxeter Parametrized

This directory proves essentially the same properties as Coxeter NonParametrized code, but for a relation that is on
List (Fin n), instead of just (List N). It is thus just a transfer of the proofs done before, with the additional step
of making sure that the bounds on values of list always hold.

## Code structure

Listed in dependency order.

 - `ReductionRel.agda` - Definition and properties of reduction relation on List (Fin n) defined in the paper.
 - `MCoxeter.agda` -  Using ReductionRel to define a symmetric relation, where l1 and l2 are related if there is a
   cospan l1 → v ← l2
 - `CoxeterMCoxeterEquiv.agda` - Proving that the MCoxeter relation as defined above is equivalent to the standard
   Coxeter relation (which includes reflexivity, transitivity and commutativity as base constructors).
