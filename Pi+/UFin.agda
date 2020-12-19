{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.UFin where

open import HoTT
open import homotopy.FinSet public

UFin = FinSet

instance
    UFin-is-gpd : has-level (S (S (S ⟨-2⟩))) UFin
    UFin-is-gpd = {!!}


Fin-S+ : ∀ {n} → Fin n → Fin (S n)
Fin-S+ (n , lt) = S n , <-ap-S lt

Fin-S+^ : ∀ {n} → (m : ℕ) → Fin n → Fin (m + n)
Fin-S+^ O <n = <n
Fin-S+^ (S m) <n = Fin-S+ (Fin-S+^ m <n)

Fin-∪ : {n m : ℕ} → (Fin n ⊔ Fin m) ≃ Fin (n + m)
Fin-∪ {n} {m} = equiv f g f-g g-f
    where f : Fin n ⊔ Fin m → Fin (n + m)
          f (inl x) = transport Fin (+-comm m n) (Fin-S+^ m x)
          f (inr x) = Fin-S^ {m} n x
          g : Fin (n + m) → Fin n ⊔ Fin m
          g = {!!}
          f-g : ∀ x → f (g x) == x
          f-g = {!!}
          g-f : ∀ x → g (f x) == x
          g-f = {!!}

_∪_ : FinSet -> FinSet → FinSet
(X , ϕ) ∪ (Y , ψ) = X ⊔ Y , {!!}
