{-# OPTIONS --without-K --rewriting #-}

module Pi+.Common.FinHelpers where

open import lib.Base
open import lib.types.Nat
open import lib.types.Fin
open import lib.PathGroupoid
open import lib.PathOver
open import lib.NType
open import lib.NType2
open import Pi+.Misc

⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
⟨_⟩ = Fin-S

S⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
S⟨ k , kltn ⟩ = S k , <-ap-S kltn

_≤^_ : {m : ℕ} -> Fin m -> Fin m -> Type₀
k ≤^ n = (k .fst) < S (n .fst)

<-down : {n k : ℕ} -> (S n < k) -> (n < k)
<-down p = <-cancel-S (ltSR p)

Fin= : {n : ℕ} -> (x y : ℕ) -> (x == y) -> (px : x < n) -> (py : y < n) -> (((x , px) :> Fin n) == ((y , py) :> Fin n))
Fin= {n} x y p xp yp = pair= p (from-transp (λ z → z < n) p (<-has-all-paths (transport (λ z → z < n) p xp) yp))

Fin-has-dec-eq-p : {n : ℕ} → has-dec-eq (Fin n)
Fin-has-dec-eq-p {n} (O , xp) (O , yp) = inl (pair= idp (<-has-all-paths xp yp))
Fin-has-dec-eq-p {n} (O , xp) (S y , yp) = inr (λ {()})
Fin-has-dec-eq-p {n} (S x , xp) (O , yp) = inr (λ {()})
Fin-has-dec-eq-p {S n} (S x , xp) (S y , yp) with (Fin-has-dec-eq-p {n} (x , <-cancel-S xp) (y , <-cancel-S yp))
... | inl q = inl (Fin= (S x) (S y) (ap S (ap fst q)) xp yp)
... | inr q = inr λ qq → q (Fin= x y (ℕ-S-is-inj x y (ap fst qq)) (<-cancel-S xp) (<-cancel-S yp))


private
  variable
    k : ℕ

fzero : Fin (S k)
fzero = (0 , O<S _)

-- Conversion back to ℕ is trivial...
toℕ : Fin k → ℕ
toℕ = fst

-- ... and injective.
toℕ-injective : ∀{fj fk : Fin k} → toℕ fj == toℕ fk → fj == fk
toℕ-injective {fj = fj} {fk} p = pair= p prop-has-all-paths-↓

S⟨⟩-inj : {n : ℕ} -> {fj fk : Fin n} → S⟨ fj ⟩ == S⟨ fk ⟩ → fj == fk
S⟨⟩-inj = toℕ-injective ∘ ℕ-S-is-inj _ _ ∘ ap toℕ
