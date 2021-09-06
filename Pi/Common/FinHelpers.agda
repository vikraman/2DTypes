{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

module Pi.Common.FinHelpers where

open import HoTT hiding (⟨_⟩)
open import Pi.Misc

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

instance
  Fin-is-set-p : {n : ℕ} → is-set (Fin n)
  Fin-is-set-p = dec-eq-is-set Fin-has-dec-eq-p

instance
  Fin1-level : is-contr (Fin 1)
  Fin1-level = has-level-in ((0 , ltS) , λ { (O , ϕ) → fin= idp ; (S n , ltSR ()) })

private
  variable
    k : ℕ

fzero : Fin (S k)
fzero = (0 , O<S _)

-- Conversion back to ℕ is trivial...
toℕ : Fin k → ℕ
toℕ = fst

-- ... and injective.
abstract
  toℕ-inj : {fj fk : Fin k} → toℕ fj == toℕ fk → fj == fk
  toℕ-inj {fj = fj} {fk} p = pair= p prop-has-all-paths-↓

  ap-toℕ-equiv : {fj fk : Fin k} → is-equiv (ap toℕ {x = fj} {y = fk})
  ap-toℕ-equiv =
    is-eq (ap toℕ) toℕ-inj (λ _ → prop-has-all-paths _ _) (λ _ → prop-has-all-paths _ _)

abstract
  S⟨⟩-inj : {n : ℕ} → {fj fk : Fin n} → S⟨ fj ⟩ == S⟨ fk ⟩ → fj == fk
  S⟨⟩-inj = toℕ-inj ∘ ℕ-S-is-inj _ _ ∘ ap toℕ

  ap-S⟨⟩-equiv : {n : ℕ} → {fj fk : Fin n} → is-equiv (ap S⟨_⟩ {x = fj} {y = fk})
  ap-S⟨⟩-equiv {n} {fj} {fk} =
    is-eq (ap S⟨_⟩) S⟨⟩-inj (λ _ → prop-has-all-paths _ _) (λ _ → prop-has-all-paths _ _)
