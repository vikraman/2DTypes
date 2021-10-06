{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi.Everything where

-- Section 4: UFin
import Pi.UFin.UFin

-- Section 5: Sn and Lehmer
import Pi.Coxeter.GeneratedGroupIso
import Pi.Coxeter.GeneratedGroupIsoGeneralised
import Pi.Coxeter.NormEquiv
import Pi.UFin.UFinLehmer2Equiv

-- Section 6: Equivalence
import Pi.Equiv.Equiv0
import Pi.Equiv.Equiv1
import Pi.Equiv.Equiv2

-- Section 7: Examples
import Pi.Examples.Examples