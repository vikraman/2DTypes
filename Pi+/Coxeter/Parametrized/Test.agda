{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Parametrized.Test where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.Equivalence
open import lib.PathGroupoid
open import lib.types.Fin
open import lib.types.List
open import lib.types.Nat

open import Pi+.Coxeter.Common.Lehmer
open import Pi+.Coxeter.Common.ListFinLListEquiv
open import Pi+.Coxeter.Common.LList
open import Pi+.Coxeter.Common.ListN
open import Pi+.Coxeter.Common.Arithmetic
open import Pi+.Coxeter.NonParametrized.ReductionRel
open import Pi+.Coxeter.NonParametrized.MCoxeter
open import Pi+.Coxeter.NonParametrized.LehmerCanonical using (only-one-canonical↔)
open import Pi+.Coxeter.NonParametrized.LehmerReduction using (Listℕ-to-Lehmer)
open import Pi+.Coxeter.Parametrized.Group
open import Pi+.Coxeter.Parametrized.Coxeter
open import Pi+.Coxeter.Parametrized.ReductionRel
open import Pi+.Coxeter.Parametrized.CoxeterMCoxeterEquiv
open import Pi+.Coxeter.Parametrized.MCoxeter
open import Pi+.Coxeter.Parametrized.Equiv

l0 : Lehmer 0
l0 = CanZ
l1 : Lehmer 1
l1 = CanS {0} CanZ {1} (s≤s z≤n)
l2 : Lehmer 2
l2 = CanS l1 {2} (s≤s (s≤s z≤n))

t1 : Sn 2
t1 = q[ (0 , ltSR (ltSR ltS)) :: 
        (0 , ltSR (ltSR ltS)) :: 
        (2 , ltS) :: 
        (1 , ltSR ltS) :: 
        (2 , ltS) :: 
        nil ]

test = (<– Lehmer≃Coxeter t1)
t = immersion test