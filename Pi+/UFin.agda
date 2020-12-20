{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.UFin where

open import HoTT
open import homotopy.FinSet public

UFin = FinSet

instance
    UFin-is-gpd : has-level (S (S (S ⟨-2⟩))) UFin
    UFin-is-gpd = ?

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

Fin-∪ : {n m : ℕ} → (Fin n ⊔ Fin m) ≃ Fin (n + m)
Fin-∪ {O} {m} = pp
  where
  lemma : Fin 0 ⊔ Fin m == Empty ⊔ Fin m
  lemma = ap (λ x -> x ⊔ Fin m) (ua Fin-equiv-Empty)

  pp =
      Fin 0 ⊔ Fin m
        ≃⟨ coe-equiv lemma ⟩
      Empty ⊔ Fin m
        ≃⟨ ⊔₁-Empty (Fin m) ⟩
      Fin m
        ≃∎
Fin-∪ {S n} {m} = pp
  where
  lemma : Fin (S n) ⊔ Fin m == (Fin n ⊔ Unit) ⊔ Fin m
  lemma = ap (λ x -> x ⊔ Fin m) (ua Fin-equiv-Coprod)

  pp =
      Fin (S n) ⊔ Fin m
        ≃⟨ coe-equiv lemma ⟩
      (Fin n ⊔ Unit) ⊔ Fin m
        ≃⟨ ⊔-assoc (Fin n) Unit (Fin m) ⟩
      Fin n ⊔ (Unit ⊔ Fin m)
        ≃⟨ coe-equiv ((ap (λ x -> Fin n ⊔ x) (ua (⊔-comm Unit (Fin m) ))))⟩
      Fin n ⊔ (Fin m ⊔ Unit)
        ≃⟨ coe-equiv ((ap (λ x -> Fin n ⊔ x) (ua Fin-equiv-Coprod))) ⁻¹⟩
      Fin n ⊔ Fin (S m)
        ≃⟨ Fin-∪ {n} {(S m)} ⟩
      Fin (n + (S m))
        ≃⟨ coe-equiv (ap Fin (+-βr n m)) ⟩
      Fin (S (n + m))
        ≃∎

_∪_ : FinSet -> FinSet → FinSet
(X , ϕ) ∪ (Y , ψ) = X ⊔ Y , Trunc-fmap2 {!   !} ϕ ψ
  where
    tx : {! ? !}
    tx = transport (SubtypeProp.prop FinSet-prop) (ua (Fin-∪ ⁻¹)) {!!}
