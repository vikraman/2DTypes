{-# OPTIONS --rewriting --without-K #-}

module Pi+.Lehmer.LehmerLevel where

open import HoTT

open import Pi+.Lehmer.Lehmer
open import Pi+.Lehmer.LehmerFinEquiv

instance
  Lehmer-O-level : is-contr (Lehmer O)
  Lehmer-O-level = has-level-in (CanZ , λ { CanZ → idp })

  Lehmer-level : {n : ℕ} → is-set (Lehmer n)
  Lehmer-level {O} = contr-is-set Lehmer-O-level
  Lehmer-level {S n} =
    let ind = LehmerInd {n}
        rec = Lehmer-level {n}
    in  equiv-preserves-level {B = Lehmer (S n)} ind {{×-level Fin-is-set rec}}
