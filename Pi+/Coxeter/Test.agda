{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

module Pi+.Coxeter.Test where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.Equivalence
open import lib.PathGroupoid
open import lib.types.Fin
open import lib.types.List
open import lib.types.Nat

open import Pi+.Lehmer.Lehmer
open import Pi+.Common.ListFinLListEquiv
open import Pi+.Common.LList
open import Pi+.Common.ListN
open import Pi+.Common.Arithmetic
open import Pi+.Coxeter.NonParametrized.ReductionRel
open import Pi+.Coxeter.NonParametrized.MCoxeter
open import Pi+.Coxeter.NonParametrized.LehmerCanonical using (only-one-canonical↔)
open import Pi+.Coxeter.NonParametrized.LehmerReduction using (Listℕ-to-Lehmer)
-- open import Pi+.Coxeter.Parametrized.Group
-- open import Pi+.Coxeter.Parametrized.Coxeter
open import Pi+.Coxeter.LehmerCoxeterEquiv as LL1
open import Pi+.Common.FinHelpers
open import Pi+.Lehmer.Lehmer2 as L2
open import Pi+.Lehmer.Lehmer2FinEquiv as LF2
open import Pi+.Coxeter.Sn
open import Pi+.UFin.BAut
open import Pi+.Misc
open import Pi+.Extra
open import Pi+.Coxeter.InvTransform

-- open import Pi+.Coxeter.Parametrized.ReductionRel
-- open import Pi+.Coxeter.Parametrized.CoxeterMCoxeterEquiv
-- open import Pi+.Coxeter.Parametrized.MCoxeter
-- open import Pi+.Coxeter.Parametrized.Equiv

-- l0 : Lehmer 0
-- l0 = CanZ
-- l1 : Lehmer 1
-- l1 = CanS {0} CanZ {1} (s≤s z≤n)
-- l2 : Lehmer 2
-- l2 = CanS l1 {2} (s≤s (s≤s z≤n))

t1 : List (Fin 4)
t1 = (2 , ltSR ltS) :: 
        (1 , ltSR (ltSR ltS)) :: 
        (3 , ltS) :: 
        (2 , ltSR ltS) :: 
        (0 , ltSR (ltSR (ltSR ltS))) :: 
        nil

t2 = –> Lehmer1-Lehmer2-equiv (immersion⁻¹ t1)

t3 : Aut (Fin 5)
t3 = <– LF2.Fin≃Lehmer t2

-- x0 = <– t3 (0 , ltSR (ltSR (ltSR (ltSR ltS)))) -- 3 -> 1 = 4 - 3
-- x1 = <– t3 (1 , ltSR (ltSR (ltSR ltS))) -- 0 -> 4 = 4 - 0
-- x2 = <– t3 (2 , ltSR (ltSR ltS)) -- 2 -> 2 = 4 - 2
-- x3 = <– t3 (3 , ltSR ltS) -- 1 -> 3 = 4 - 1
-- x4 = <– t3 (4 , ltS) -- 4 -> 0 = 4 - 4

-- -- ll = {!   !}



sss = inv-transform t3

y0 = <– sss (0 , ltSR (ltSR (ltSR (ltSR ltS)))) -- 3
y1 = <– sss (1 , ltSR (ltSR (ltSR ltS))) -- 0
y2 = <– sss (2 , ltSR (ltSR ltS)) -- 4
y3 = <– sss (3 , ltSR ltS) -- 1
y4 = <– sss (4 , ltS) -- 2
