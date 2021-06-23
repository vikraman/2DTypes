{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

module Pi+.Coxeter.NormEquiv where

open import HoTT

open import Pi+.Coxeter.Sn
open import Pi+.Coxeter.Coxeter
open import Pi+.Coxeter.LehmerSnEquiv
open import Pi+.Coxeter.LehmerCoxeterEquiv renaming (immersion to immersionFull)
open import Pi+.Coxeter.Norm
open import Pi+.Lehmer.Lehmer2 as L2
open import Pi+.Lehmer.Lehmer as L1
open import Pi+.Common.Arithmetic
open import Pi+.Common.InequalityEquiv

open import Pi+.Extra
open import Pi+.Misc

variable
    n : ℕ

_↓_ : (n : ℕ) -> (k : ℕ) -> List (Fin (S (k + n)))
n ↓ 0 = nil
n ↓ (S k) = ((k + n) , ltSR ltS) :: map Fin-S (n ↓ k)

immersion : L2.Lehmer n → List (Fin (S n))
immersion {O} c = nil
immersion {S n} ((k , ϕ) , c) =
    let x = ((S n  ∸ k) ↓ k)
        ψ : k + (S n ∸ k) == S n
        ψ = plus-minus {p = k} {q = S n} (≤-down2 (–> <N≃< ϕ))
    in  map Fin-S (immersion c) ++ transport (List ∘ Fin ∘ S) ψ x

immersion' : L1.Lehmer n → List (Fin (S n))
immersion' {O} CanZ = nil
immersion' {S n} (CanS c {k} ϕ) =
  let x = ((S n  ∸ k) ↓ k)
      ψ : k + (S n ∸ k) == S n
      ψ = plus-minus {p = k} {q = S n} ϕ
  in map Fin-S (immersion' c) ++ transport (List ∘ Fin ∘ S) ψ x

-- immersion {S n} (CanS l {r} r≤1+n) = (immersion l) ++ (((S n) ∸ r) ↓ r)

norm-immersion : {n : ℕ} (c : L1.Lehmer n) → norm (immersionFull c) == immersionFull c
norm-immersion {O} CanZ = idp
norm-immersion {S n} c = TODO-

Lemer≃im-norm : {n : ℕ} → L1.Lehmer n ≃ im -1 (norm {n})
Lemer≃im-norm = Sn≃im-norm ∘e Lehmer≃Coxeter
