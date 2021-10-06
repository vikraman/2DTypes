{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi.Everything where

-- Section 4: UFin
import Pi.UFin.UFin

-- Section 5: Sn and Lehmer

-- Coxeter Relations and Sn
import Pi.Coxeter.Coxeter
import Pi.Coxeter.Sn

-- Sn as a group presentation
import Pi.Coxeter.GeneratedGroupIso
import Pi.Coxeter.GeneratedGroupIsoGeneralised

-- Lehmer codes
import Pi.Lehmer.Lehmer2

-- Normalisation of words in Sn
import Pi.Coxeter.Norm
import Pi.Coxeter.NormEquiv

-- Equivalence with Lehmer codes
import Pi.UFin.UFinLehmer2Equiv

-- Section 6: Equivalence

-- Pi and Pi+
import Pi.Equiv.Translation2

-- Pi+ and Pi^
import Pi.Equiv.Equiv0Hat
import Pi.Equiv.Equiv1Hat
import Pi.Equiv.Equiv2Hat

-- Pi^ and UFin
import Pi.Equiv.Equiv0Norm
import Pi.Equiv.Equiv1Norm
import Pi.Equiv.Equiv2Norm

-- Pi+ and UFin
import Pi.Equiv.Equiv0
import Pi.Equiv.Equiv1
import Pi.Equiv.Equiv2

-- Section 7: Examples
import Pi.Examples.Examples