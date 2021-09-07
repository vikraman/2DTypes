# README - Equiv

This directory contains the proofs of equivalence between all three levels of Pi syntax and their respective semantics.

## Code structure

  - `Equiv0.agda`: The proof of equivalence between Pi+ types and 0-cells in UFin. A composition of:
    - `Equiv0Hat.agda`: The proof of equivalence between Pi+ types and Pi^ types.
    - `Equiv0Norm.agda`: The proof of equivalence between Pi^ types (natural numbers) and 0-cells in UFin.
  - `Equiv1.agda`: The proof of equivalence between the 1-combinators of Pi+ and 1-paths in UFin. A composition of:
    - `Equiv1Hat.agda`: The proof of equivalence between Pi+ 1-combinators and Pi^ 1-combinators.
    - `Equiv1Norm.agda`: The proof of equivalence between Pi^ 1-combinators and 1-cells in UFin.
  - `Equiv2.agda`: The proof of equivalence between the 2-combinators of Pi+ and 2-paths in UFin. A composition of:
    - `Equiv2Hat.agda`: The proof of equivalence between Pi+ 1-combinators and Pi^ 1-combinators.
    - `Equiv2Norm.agda`: The proof of equivalence between Pi^ 2-combinators and 2-paths in UFin.
  - `Translation.agda`, `Translation2.agda`: Translation of Pi to Pi+ and back.