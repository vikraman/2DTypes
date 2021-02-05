{-# OPTIONS --rewriting --without-K #-}

module Pi+.Lehmer.LehmerLevel where

open import HoTT

open import Pi+.Lehmer.Lehmer
open import Pi+.Lehmer.LehmerFinEquiv

instance
  Lehmer-level : {n : ℕ} → is-set (Lehmer n)
  Lehmer-level {O} = contr-is-set (has-level-in (CanZ , (λ {CanZ → idp})))
  Lehmer-level {S n} = 
    let ind = LehmerInd {n}
        rec = Lehmer-level {n}
    in  equiv-preserves-level {B = Lehmer (S n)} ind {{×-level Fin-is-set rec}}