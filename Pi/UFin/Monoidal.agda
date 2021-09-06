{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi.UFin.Monoidal where

open import HoTT
open import homotopy.FinSet public

open import Pi.UFin.Base
open import Pi.Misc as N
open import Pi.Extra

⊔-comm : (A B : Type₀) -> (A ⊔ B) ≃ (B ⊔ A)
⊔-comm A B = equiv f g f-g g-f
  where f : (A ⊔ B) -> (B ⊔ A)
        f (inl x) = inr x
        f (inr x) = inl x
        g : (B ⊔ A) -> (A ⊔ B)
        g (inl x) = inr x
        g (inr x) = inl x
        f-g : ∀ x -> f (g x) == x
        f-g (inl x) = idp
        f-g (inr x) = idp
        g-f : ∀ x -> g (f x) == x
        g-f (inl x) = idp
        g-f (inr x) = idp

⊔-assoc : (A B C : Type₀) -> (A ⊔ B) ⊔ C ≃ A ⊔ (B ⊔ C)
⊔-assoc A B C = equiv f g f-g g-f
  where f : (A ⊔ B) ⊔ C -> A ⊔ (B ⊔ C)
        f (inl (inl x)) = inl x
        f (inl (inr x)) = inr (inl x)
        f (inr x) = inr (inr x)
        g : A ⊔ (B ⊔ C) -> (A ⊔ B) ⊔ C
        g (inl x) = inl (inl x)
        g (inr (inl x)) = inl (inr x)
        g (inr (inr x)) = inr x
        f-g : ∀ x -> f (g x) == x
        f-g (inl x) = idp
        f-g (inr (inl x)) = idp
        f-g (inr (inr x)) = idp
        g-f : ∀ x -> g (f x) == x
        g-f (inl (inl x)) = idp
        g-f (inl (inr x)) = idp
        g-f (inr x) = idp

⊔-≃ : {A B C D : Type₀} → (A ≃ B) → (C ≃ D) → (A ⊔ C) ≃ (B ⊔ D)
⊔-≃ {A} {B} {C} {D} e₁ e₂ = equiv f g f-g g-f
  where f : A ⊔ C → B ⊔ D
        f (inl a) = inl (–> e₁ a)
        f (inr c) = inr (–> e₂ c)
        g : B ⊔ D → A ⊔ C
        g (inl b) = inl (<– e₁ b)
        g (inr d) = inr (<– e₂ d)
        f-g : (x : B ⊔ D) → f (g x) == x
        f-g (inl b) = ap inl (<–-inv-r e₁ b)
        f-g (inr d) = ap inr (<–-inv-r e₂ d)
        g-f : (x : A ⊔ C) → g (f x) == x
        g-f (inl a) = ap inl (<–-inv-l e₁ a)
        g-f (inr c) = ap inr (<–-inv-l e₂ c)

Fin-⊔ : {n m : ℕ} → (Fin n ⊔ Fin m) ≃ Fin (n + m)
Fin-⊔ {O} {m} =
  ⊔₁-Empty (Fin m) ∘e
  ⊔-≃ Fin-equiv-Empty (ide (Fin m))
Fin-⊔ {S n} {m} =
  Fin-equiv-Coprod {n + m} ⁻¹ ∘e
  ⊔-≃ (Fin-⊔ {n} {m}) (ide ⊤) ∘e
  ⊔-assoc (Fin n) (Fin m) ⊤ ⁻¹ ∘e
  ⊔-≃ (ide (Fin n)) (⊔-comm ⊤ (Fin m)) ∘e
  ⊔-assoc (Fin n) ⊤ (Fin m) ∘e
  ⊔-≃ (Fin-equiv-Coprod {n}) (ide (Fin m))

_∪_ : FinSet -> FinSet → FinSet
(X , ϕ) ∪ (Y , ψ) = X ⊔ Y , Trunc-fmap2 tx ϕ ψ
  where
    tx : Σ ℕ (λ n → Fin n == X) → Σ ℕ (λ n → Fin n == Y) → Σ ℕ (λ n → Fin n == X ⊔ Y)
    tx (n , α) (m , β)= (n + m) , ua ((Fin-⊔ ∘e transport2-equiv (λ x y ->  x ⊔ y) (! α) (! β)) ⁻¹)

×₁-Empty : ∀ {i} (A : Type i) → Empty × A ≃ Empty
×₁-Empty A = equiv (λ { ((), a) }) (λ ()) (λ ()) (λ { ((), a) })

×₁-Unit : ∀ {i} (A : Type i) → Unit × A ≃ A
×₁-Unit A = equiv snd (λ a → tt , a) (λ a → idp) (λ { (tt , a) → idp })

×-≃ : {A B C D : Type₀} → (A ≃ B) → (C ≃ D) → (A × C) ≃ (B × D)
×-≃ {A} {B} {C} {D} e₁ e₂ = equiv f g f-g g-f
  where f : (A × C) → (B × D)
        f (a , c) = –> e₁ a , –> e₂ c
        g : (B × D) → (A × C)
        g (b , d) = <– e₁ b , <– e₂ d
        f-g : (x : B × D) → f (g x) == x
        f-g (b , d) = pair= (<–-inv-r e₁ b) (↓-cst-in (<–-inv-r e₂ d))
        g-f : (x : A × C) → g (f x) == x
        g-f (a , c) = pair= (<–-inv-l e₁ a) (↓-cst-in (<–-inv-l e₂ c))

×-⊔-distrib : (A B C : Type₀) → (A ⊔ B) × C ≃ (A × C) ⊔ (B × C)
×-⊔-distrib A B C = equiv f g f-g g-f
  where f : (A ⊔ B) × C → (A × C) ⊔ (B × C)
        f (inl a , c) = inl (a , c)
        f (inr b , c) = inr (b , c)
        g : (A × C) ⊔ (B × C) → (A ⊔ B) × C
        g (inl (a , c)) = inl a , c
        g (inr (b , c)) = inr b , c
        f-g : (x : (A × C) ⊔ B × C) → f (g x) == x
        f-g (inl (a , c)) = idp
        f-g (inr (b , c)) = idp
        g-f : (x : (A ⊔ B) × C) → g (f x) == x
        g-f (inl a , c) = idp
        g-f (inr b , c) = idp

Fin-× : {n m : ℕ} → (Fin n × Fin m) ≃ Fin (n N.* m)
Fin-× {O} {m} =
  Fin-equiv-Empty ⁻¹ ∘e
  ×₁-Empty (Fin m) ∘e
  ×-≃ Fin-equiv-Empty (ide (Fin m))
Fin-× {S n} {m} =
  Fin-⊔ {m} {n N.* m} ∘e
  ⊔-≃ (ide (Fin m)) (Fin-× {n} {m}) ∘e
  ⊔-comm (Fin n × Fin m) (Fin m) ∘e
  ⊔-≃ (ide _) (×₁-Unit (Fin m)) ∘e
  ×-⊔-distrib (Fin n) ⊤ (Fin m) ∘e
  ×-≃ Fin-equiv-Coprod (ide (Fin m))
