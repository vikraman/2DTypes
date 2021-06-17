{-# OPTIONS --rewriting --without-K #-}

module Pi+.Lehmer.Lehmer2Level where

open import HoTT

open import Pi+.Lehmer.Lehmer2
open import Pi+.Lehmer.Lehmer2FinEquiv
import Pi+.Lehmer.LehmerLevel as L1

instance

  Lehmer-level : {n : ℕ} → is-set (Lehmer n)
  Lehmer-level {n} = equiv-preserves-level {lzero} Lehmer1-Lehmer2-equiv {{L1.Lehmer-level}}