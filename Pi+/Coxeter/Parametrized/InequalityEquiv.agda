{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Parametrized.InequalityEquiv where

open import lib.Base
open import lib.types.Nat using (_+_; O<S; <-ap-S; <-has-all-paths) renaming (_<_ to _<N_)
open import lib.Equivalence

open import Pi+.Coxeter.Common.Arithmetic


<N≃< : {a b : ℕ} -> (a <N b) ≃ (a < b)
<N≃< = equiv f g (λ x → ≤-has-all-paths (f (g x)) x) (λ x → <-has-all-paths (g (f x)) x)
  where
    f : {a b : ℕ} -> a <N b -> a < b
    f _<N_.ltS = rrr
    f (_<N_.ltSR p) = ≤-up (f p)

    g : {a b : ℕ} -> a < b -> a <N b
    g {O} {.(S _)} (s≤s p) = O<S _
    g {S a} {S (S b)} (s≤s p) = let r = g p in <-ap-S r
