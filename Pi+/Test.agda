{-# OPTIONS --without-K --allow-unsolved-metas --rewriting #-}

module Pi+.Test where

open import HoTT

open import Pi+.Lehmer.Lehmer
open import Pi+.Lehmer.LehmerFinEquiv
open import Pi+.Extra
open import Pi+.UFin
open import Pi+.Common.Arithmetic


cn0 = –> (<– Fin≃Lehmer (CanS (CanS (CanS CanZ {1} (s≤s z≤n)) {0} z≤n) {2} (s≤s (s≤s z≤n)))) (0 , (ltSR (ltSR (ltSR ltS))))
cn1 = –> (<– Fin≃Lehmer (CanS (CanS (CanS CanZ {1} (s≤s z≤n)) {0} z≤n) {2} (s≤s (s≤s z≤n)))) (1 , (ltSR (ltSR ltS)))
cn2 = –> (<– Fin≃Lehmer (CanS (CanS (CanS CanZ {1} (s≤s z≤n)) {0} z≤n) {2} (s≤s (s≤s z≤n)))) (2 , (ltSR ltS))
cn3 = –> (<– (Fin≃Lehmer {n = 3}) (CanS (CanS (CanS CanZ {1} (s≤s z≤n)) {0} z≤n) {2} (s≤s (s≤s z≤n)))) (3 , ltS)
