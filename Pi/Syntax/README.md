# README - Syntax

This directory contains sytnax specifications for all the flavous of Pi we use in the proof.

## Code structure

  - `Pi.agda`: full Pi language (sum and product types)
  - `Pi+`: Pi language restricted to sum types (O, I, +)
    - `NonIndexed.agda`: the base syntax
    - `Indexed.agda`: the syntax where types are indexed by their cardinality
  - `Pi^.agda`: Strictified Pi syntax with natural numbers for types