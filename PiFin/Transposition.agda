module PiFin.Transposition where

open import Type using (Type; Type₀)
open import Zero
open import One
open import Paths using (_==_; refl)
open import Functions using (_∘_; id)
open import Homotopies using (_∼_)
open import DependentSum using (Σ; _×_; _,_; p₁; p₂)
open import Coproduct
open import Equivalences using (_≃_)

open import NaturalNumbers

open import PiFin.EmbeddingsInUniverse using (module UnivalentUniverseOfFiniteTypes)
open UnivalentUniverseOfFiniteTypes using (El)

open import PiFin.CPerm
open import PiFin.Syntax

_≤_ : {n : ℕ} → El n → El n → Type₀
_≤_ {0} ()
_≤_ {succ _} (i₁ 0₁) _     = 𝟙
_≤_ {succ _} (i₂ a) (i₂ b) = a ≤ b
_ ≤ _ = 𝟘

Transposition : ℕ → Type₀
Transposition n = Σ (El n × El n) (λ { (i , j) → i ≤ j })

data List {ℓ} (A : Type ℓ) : Type ℓ where
  [] : List A
  _∷_ : A → List A → List A

Transposition* : ℕ → Type₀
Transposition* n = List (Transposition n)

postulate
  swapFin : {n : ℕ} → (a b : El n) → (leq : a ≤ b) → fromSize n ⟷ fromSize n
{-swapFin {0} ()
swapFin {succ _} fzero fzero 0₁ = id⟷
swapFin {succ (succ _)} fzero (fsucc fzero) 0₁ = assocl₊ ◎ ((swap₊ ⊕ id⟷) ◎ assocr₊)
swapFin {succ (succ _)} fzero (fsucc (fsucc b)) 0₁ =
  (assocl₊ ◎ ((swap₊ ⊕ id⟷) ◎ assocr₊)) ◎
  ((id⟷ ⊕ swapFin fzero (fsucc b) 0₁) ◎
  (assocl₊ ◎ ((swap₊ ⊕ id⟷) ◎ assocr₊)))
swapFin {succ _} (fsucc a) fzero ()
swapFin {succ _} (fsucc a) (fsucc b) leq = id⟷ ⊕ swapFin a b leq
swapFin {succ _} fzero (fsucc _) 0₁ = {!!}-}

-- https://groupprops.subwiki.org/wiki/Transpositions_generate_the_finitary_symmetric_group
postulate
  trans-perm-equiv : {m n : ℕ} {p : m == n} → Transposition* m ≃ CPerm m n

perm-to-trans : {m n : ℕ} {p : m == n} → CPerm m n → Transposition* m
perm-to-trans {p = p} = p₁ (p₂ (trans-perm-equiv {p = p}))

transposition*2c : (m n : ℕ) (m≡n : m == n) → Transposition* m → fromSize m ⟷ fromSize n
transposition*2c m n (refl _) [] = id⟷
transposition*2c m n (refl _) (((i , j) , leq) ∷ π) =
  swapFin i j leq ◎ transposition*2c n n (refl _) π

-- Permutation to combinator
reify : {m n : ℕ} {p : m == n} → CPerm m n → fromSize m ⟷ fromSize n
reify {m} {n} {p} π = transposition*2c m n p (perm-to-trans {p = p} π)
