# README - Lehmer

This directory contains code defining and proving various properties of Lehmer codes.

Part of the code proving that Lehmer is equivalent to Aut(Fin n) modified from https://github.com/agda/cubical  
License in included in the `LICENSE_cubical` file.

## Code structure

  - `FinExcept.agda`: The definition of Fin^{-1}, as given in the paper
  - `Lehmer.agda`: a definiton of Lehmer codes
  - `Lehmer2.agda`: alternative definiton of Lehmer codes
  - `LehmerFinEquiv.agda`, `Lehmer2FinEquiv.agda` : proofs that Lehmer codes are equivalent to automorphisms on (Fin n)