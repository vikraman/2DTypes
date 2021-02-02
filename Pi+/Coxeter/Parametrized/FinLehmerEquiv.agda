{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Parametrized.FinLehmerEquiv where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.Equivalence
open import lib.Univalence
open import lib.PathGroupoid
open import lib.PathOver
open import lib.types.Fin
open import lib.types.List
open import lib.types.Sigma
open import lib.types.Coproduct
open import lib.types.Unit
open import lib.types.Nat using (<-has-all-paths)

open import Pi+.Coxeter.Common.Lehmer
open import Pi+.Coxeter.Common.InequalityEquiv
open import Pi+.Coxeter.Common.Arithmetic

open import Pi+.UFin.Monoidal
open import Pi+.Extra

≤→< : {k n : ℕ} -> (k ≤ n) -> (k < S n)
≤→< z≤n = s≤s z≤n
≤→< (s≤s p) = s≤s (≤→< p)

LehmerInd : {n : ℕ} -> (Fin (S (S n))) × Lehmer n ≃ Lehmer (S n)
LehmerInd {n} = equiv f g f-g g-f
    where
    f : _
    f ((x , p) , l) = CanS l (≤-down2 ((–> <N≃< p)))
    g : _
    g (CanS l {r} p) = (r , <– <N≃< (≤→< p)) , l
    f-g : _
    f-g (CanS l {r} p) = ap (CanS l) (≤-has-all-paths _ _)
    g-f : _
    g-f ((x , p) , l) = pair= (pair= idp (<-has-all-paths _ _)) (↓-cst-in idp)

Coprod-≃ : {A B C : Type₀} -> (A ≃ B) -> (A ⊔ C) ≃ (B ⊔ C)
Coprod-≃ = TODO

keyLemma : {n : ℕ} -> (Fin (S n) ≃ Fin (S n)) ≃ (Fin (S n) × (Fin n ≃ Fin n))
keyLemma {n} = {!   !}

Fin1≃Unit : Fin 1 ≃ Unit
Fin1≃Unit = ⊔₁-Empty ⊤ ∘e Coprod-≃ Fin-equiv-Empty ∘e Fin-equiv-Coprod

Fin1≃isContr : is-contr (Fin 1 ≃ Fin 1)
Fin1≃isContr = ≃-contr (equiv-preserves-level (Fin1≃Unit ⁻¹)) (equiv-preserves-level (Fin1≃Unit ⁻¹))

Fin≃Lehmer-base : (Fin 1 ≃ Fin 1) ≃ Lehmer O
Fin≃Lehmer-base = equiv (λ _ → CanZ) (λ CanZ → coe-equiv idp) (λ {CanZ → idp}) λ x → contr-has-all-paths {{Fin1≃isContr}} _ _

Fin≃Lehmer : {n : ℕ} -> (Fin (S n) ≃ Fin (S n)) ≃ Lehmer n
Fin≃Lehmer {O} = Fin≃Lehmer-base
Fin≃Lehmer {S n} =
        Fin (S (S n)) ≃ Fin (S (S n)) ≃⟨ keyLemma ⟩
        Fin (S (S n)) × (Fin (S n) ≃ Fin (S n)) ≃⟨ _ , (×-isemap-r _ (snd (Fin≃Lehmer {n}))) ⟩
        Fin (S (S n)) × Lehmer n ≃⟨ LehmerInd ⟩
        Lehmer (S n) ≃∎