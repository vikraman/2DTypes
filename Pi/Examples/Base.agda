{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

module Pi.Examples.Base where

open import HoTT hiding (_<_ ; ltS ; ltSR ; _+_ ; _×_ ; _++_) public
import lib.types.Nat as N
import lib.types.Sigma as S

open import Pi.UFin.BAut
open import Pi.UFin.UFin as UFin
open import Pi.Common.Misc
open import Pi.Common.Extra

open import Pi.Syntax.Pi+.Indexed as Pi+
open import Pi.Syntax.Pi^ as Pi^
open import Pi.Syntax.Pi^Helpers as Pi^
open import Pi.Syntax.Pi as Pi
open import Pi.Equiv.Translation2
import Pi.Equiv.Equiv1 as Pi+
import Pi.Equiv.Equiv0Hat as Pi^
import Pi.Equiv.Equiv1Hat as Pi^
import Pi.Equiv.Equiv0Norm as Pi^
import Pi.Equiv.Equiv1Norm as Pi^
open import Pi.UFin.UFin
open import Pi.UFin.Monoidal
open import Pi.Common.FinHelpers
open import Pi.Lehmer.FinExcept

variable
  m n o p q r : ℕ

instance
  ltS : {m : ℕ} → m N.< (S m)
  ltS = N.ltS
  ltSR : {m n : ℕ} → {{m N.< n}} → m N.< (S n)
  ltSR {m} {n} {{ϕ}} = N.ltSR ϕ


⟦_⟧ : Pi.U → Type₀
⟦ O ⟧ = ⊥
⟦ I ⟧ = ⊤
⟦ t₁ + t₂ ⟧ = ⟦ t₁ ⟧ ⊔ ⟦ t₂ ⟧
⟦ t₁ × t₂ ⟧ = ⟦ t₁ ⟧ S.× ⟦ t₂ ⟧

⟦_⟧+ : {n : ℕ} → Pi+.U n → Type₀
⟦ O ⟧+ = ⊥
⟦ I ⟧+ = ⊤
⟦ t₁ + t₂ ⟧+ = ⟦ t₁ ⟧+ ⊔ ⟦ t₂ ⟧+

⟦_⟧^ : ℕ → Type₀
⟦ O ⟧^ = ⊥
⟦ S n ⟧^ = ⊤ ⊔ ⟦ n ⟧^


Fin-eval₀-+ : ∀ {t₁ t₂} → Fin (eval₀ t₁ N.+ eval₀ t₂) ≃ Fin (eval₀ (t₁ + t₂))
Fin-eval₀-+ = ide _

Fin-≃ : ∀ {m n} → (n == m) → (Fin n ≃ Fin m)
Fin-≃ {O} {O} p = ide _
Fin-≃ {S n} {S m} p = Fin-equiv-Coprod ⁻¹ ∘e  ⊔-≃ (Fin-≃ (N.ℕ-S-is-inj _ _ p)) (ide ⊤) ∘e Fin-equiv-Coprod

Fin-eval₀ : ∀ {t₁ t₂} → Fin (eval₀ t₁ Pi.Common.Misc.* eval₀ t₂) ≃ Fin (eval₀ (t₁ × t₂))
Fin-eval₀ {t₁} {t₂} = Fin-≃ (! (eval₀-* {t₁} {t₂}))

⟦-⟧-eval₀ : {X : Pi.U} → ⟦ X ⟧ ≃ Fin (eval₀ X)
⟦-⟧-eval₀ {O} =
  Fin-equiv-Empty ⁻¹
⟦-⟧-eval₀ {I} =
  contr-equiv-Unit Fin1-level ⁻¹
⟦-⟧-eval₀ {t₁ + t₂} =
  Fin-⊔ {eval₀ t₁} {eval₀ t₂} ∘e
  ⊔-≃ (⟦-⟧-eval₀ {t₁}) (⟦-⟧-eval₀ {t₂})
⟦-⟧-eval₀ {t₁ × t₂} =
    Fin-eval₀ {t₁} {t₂} ∘e
    Fin-× {eval₀ t₁} {eval₀ t₂} ∘e
    ×-≃ (⟦-⟧-eval₀ {t₁}) (⟦-⟧-eval₀ {t₂})

⟦-⟧+-eval₀ : {n : ℕ} → {X : Pi+.U n} → ⟦ X ⟧+ ≃ Fin (Pi^.eval^₀ X)
⟦-⟧+-eval₀ {X = O} =
  Fin-equiv-Empty ⁻¹
⟦-⟧+-eval₀ {X = I} =
  contr-equiv-Unit Fin1-level ⁻¹
⟦-⟧+-eval₀ {X = t₁ + t₂} =
  Fin-⊔ {Pi^.eval^₀ t₁} {Pi^.eval^₀ t₂} ∘e
  ⊔-≃ (⟦-⟧+-eval₀ {X = t₁}) (⟦-⟧+-eval₀ {X = t₂})

⟦-⟧^-eval₀ : ∀ {n} → ⟦ n ⟧^ ≃ Fin n
⟦-⟧^-eval₀ {O} = Fin-equiv-Empty ⁻¹
⟦-⟧^-eval₀ {S n} = (Fin-equiv-Coprod ⁻¹ ∘e ⊔-comm ⊤ (Fin n)) ∘e ⊔-≃ (ide ⊤) (⟦-⟧^-eval₀ {n})


𝟚 : Pi.U
𝟚 = I + I

𝟜+ : Pi+.U 4
𝟜+ = I + I + I + I + O

𝟠+ : Pi+.U 8
𝟠+ = I + I + I + I + I + I + I + I + O

𝟙𝟞+ : Pi+.U 16
𝟙𝟞+ = I + I + I + I + I + I + I + I + I + I + I + I + I + I + I + I + O

𝔹 : ℕ → Pi.U
𝔹 O = I
𝔹 (S O) = 𝟚
𝔹 (S (S n)) = 𝟚 × 𝔹 (S n)


test0 : ⟦ 𝟚 Pi.+ 𝟚 ⟧ → Fin 4
test0 = –> ⟦-⟧-eval₀

_ : (test0 (inr (inr tt)) == 0) S.×
    (test0 (inr (inl tt)) == 1) S.×
    (test0 (inl (inr tt)) == 2) S.×
    (test0 (inl (inl tt)) == 3)
_ = fin= idp , fin= idp , fin= idp , fin= idp

test1 : ⟦ 𝔹 2 ⟧ → Fin 4
test1 = –> ⟦-⟧-eval₀

_ : (test1 (inr tt , inr tt) == 0) S.×
    (test1 (inr tt , inl tt) == 1) S.×
    (test1 (inl tt , inr tt) == 2) S.×
    (test1 (inl tt , inl tt) == 3)
_ = fin= idp , fin= idp , fin= idp , fin= idp

interp' : {X : Pi.U} (c : X Pi.⟷₁ X) → ⟦ X ⟧ ≃ ⟦ X ⟧
interp' c = ⟦-⟧-eval₀ ⁻¹ ∘e Pi^.evalNorm₁ (eval₁ c) ∘e ⟦-⟧-eval₀

-- This defines a convenient notation for writing extensional permutations.

infixr 60 _::_

data Vec {i} (A : Type i) : ℕ → Type i where
  nil : Vec A 0
  _::_ : {n : ℕ} → A → Vec A n → Vec A (S n)

tabulate : ∀ {i} {A : Type i} {n : ℕ} → (Fin n → A) → Vec A n
tabulate {n = O} f = nil
tabulate {n = S n} f = f (0 , O<S n) :: tabulate (f ∘ S⟨_⟩)

allFin : (n : ℕ) → Vec (Fin n) n
allFin n = tabulate (idf (Fin n))

lookup : ∀ {i} {A : Type i} {n : ℕ} → Vec A n → (Fin n → A)
lookup {n = S n} (x :: xs) (O , ϕ) = x
lookup {n = S n} (x :: xs) (S k , ϕ) = lookup xs (k , <-cancel-S ϕ)

-- example permutation in paper
private
  f : Fin 8 → Fin 8
  f = lookup (0 :: 5 :: 6 :: 7 :: 4 :: 1 :: 2 :: 3 :: nil)
