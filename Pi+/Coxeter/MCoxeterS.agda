{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.MCoxeterS where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.PathGroupoid

open import Pi+.Misc
open import Pi+.Coxeter.Arithmetic
open import Pi+.Coxeter.Lists
open import Pi+.Coxeter.MCoxeter
open import Pi+.Coxeter.ReductionRel
open import Pi+.Coxeter.Diamond

data _≃s_ : List -> List -> Type₀ where
    cancel≃s : {n : ℕ} -> (l r m mf : List) -> (defm : m == l ++ n :: n :: r) -> (defmf : mf == l ++ r) -> (m ≃s mf)
    swap≃s : {n : ℕ} -> {k : ℕ} -> (S k < n) ->  (l r m mf : List) -> (defm : m == l ++ n :: k :: r) -> (defmf : mf == l ++ k :: n :: r) -> (m ≃s mf)
    long≃s : {n : ℕ} -> (k : ℕ) -> (l r m mf : List) -> (defm : m == l ++ (n ↓ (2 + k)) ++ (1 + k + n) :: r) -> (defmf : mf == l ++ (k + n) :: (n ↓ (2 + k)) ++ r) -> (m ≃s mf)
    comm≃s : {m1 m2 : List} -> (m1 ≃s m2) -> (m2 ≃s m1)

data _≃s*_ : List -> List -> Type₀ where
    idp≃s : {m : List} -> m ≃s* m
    trans≃s : {m1 m2 m3 : List} -> (m1 ≃s m2) -> (m2 ≃s* m3) -> m1 ≃s* m3


trans≃s* : {m1 m2 m3 : List} -> (m1 ≃s* m2) -> (m2 ≃s* m3) -> m1 ≃s* m3
trans≃s* idp≃s p = p
trans≃s* (trans≃s x q) p = trans≃s x (trans≃s* q p)

comm≃s* : {m1 m2 m3 : List} -> (m1 ≃s* m2) -> m2 ≃s* m1
comm≃s* idp≃s = idp≃s
comm≃s* {m1} {m2} {m3} (trans≃s x q) = 
    let x' = comm≃s x
        q' = comm≃s* {_} {_} {m2} q
    in  trans≃s* q' (trans≃s (comm≃s x) idp≃s)

mcoxeters->mcoxeter : {m1 m2 : List} -> (m1 ≃s m2) -> (m1 ≃ m2)
mcoxeters->mcoxeter {m1} {m2} (cancel≃s l r .m1 .m2 defm defmf) = comm≅ {_} {_} {m2} (trans≅ (cancel≅ l r m1 m2 defm defmf) idp) idp
mcoxeters->mcoxeter {m1} {m2} (swap≃s x l r .m1 .m2 defm defmf) = comm≅ {_} {_} {m2} (trans≅ (swap≅ x l r m1 m2 defm defmf) idp) idp
mcoxeters->mcoxeter {m1} {m2} (long≃s k l r .m1 .m2 defm defmf) = comm≅ {_} {_} {m2} (trans≅ (long≅ k l r m1 m2 defm defmf) idp) idp
mcoxeters->mcoxeter {m1} {m2} (comm≃s {.m2} {.m1} p) with mcoxeters->mcoxeter p
... | comm≅ {_} {_} {mf} p1 p2 = comm≅ {_} {_} {mf} p2 p1 

mcoxeters*->mcoxeter : {m1 m2 : List} -> (m1 ≃s* m2) -> (m1 ≃ m2)
mcoxeters*->mcoxeter {m1} {.m1} idp≃s = comm≅ idp idp
mcoxeters*->mcoxeter {m1} {m2} (trans≃s x p) with mcoxeters*->mcoxeter p
... | comm≅ {m3} {m2} {mf} p1 p2 with mcoxeters->mcoxeter x
...     | comm≅ {m1} {m3} {mf'} p3 p4 with diamond-full p1 p4
...         | m , (pmf , pmf') = comm≅ {_} {_} {m} (trans p3 pmf') (trans p2 pmf)


mcoxeter≅->mcoxeters* : {m1 m2 : List} -> (m1 ≅ m2) -> (m1 ≃s m2)
mcoxeter≅->mcoxeters* {m1} {m2} (cancel≅ l r .m1 .m2 defm defmf) = cancel≃s l r m1 m2 defm defmf
mcoxeter≅->mcoxeters* {m1} {m2} (swap≅ x l r .m1 .m2 defm defmf) = swap≃s x l r m1 m2 defm defmf
mcoxeter≅->mcoxeters* {m1} {m2} (long≅ k l r .m1 .m2 defm defmf) = long≃s k l r m1 m2 defm defmf

mcoxeter≅*->mcoxeters* : {m1 m2 : List} -> (m1 ≅* m2) -> (m1 ≃s* m2)
mcoxeter≅*->mcoxeters* {m1} {.m1} idp = idp≃s
mcoxeter≅*->mcoxeters* {m1} {m2} (trans≅ x p) = trans≃s (mcoxeter≅->mcoxeters* x) (mcoxeter≅*->mcoxeters* p)

mcoxeter->mcoxeters* : {m1 m2 : List} -> (m1 ≃ m2) -> (m1 ≃s* m2)
mcoxeter->mcoxeters* {m1} {m2} (comm≅ {_} {_} {mf} p1 p2) = 
    let q1 = mcoxeter≅*->mcoxeters* p1
        q2 = mcoxeter≅*->mcoxeters* p2
    in  trans≃s* q1 (comm≃s* {_} {_} {mf} q2)