{-# OPTIONS --rewriting --without-K --overlapping-instances #-}

module Pi+.Lehmer.LehmerFinEquiv where

open import HoTT hiding (_≤_; _<_; ≤-has-all-paths)

open import Pi+.Extra
open import Pi+.Lehmer.FinHelpers
open import Pi+.Lehmer.Lehmer
open import Pi+.Common.InequalityEquiv
open import Pi+.Common.Arithmetic
open import Pi+.Coxeter.InvTransform

open import Pi+.UFin.BAut
open import Pi+.Misc
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

Coprod-≃-r : {A B C : Type₀} -> (A ≃ B) -> (A ⊔ C) ≃ (B ⊔ C)
Coprod-≃-r e = equiv f g f-g g-f
    where
    f : _
    f (inr x) = inr x
    f (inl x) = inl (–> e x)
    g : _
    g (inr x) = inr x
    g (inl x) = inl (<– e x)
    f-g : _
    f-g (inr x) = idp
    f-g (inl x) = ap inl (<–-inv-r e x)
    g-f : _
    g-f (inr x) = idp
    g-f (inl x) = ap inl (<–-inv-l e x)

instance
  Lehmer-O-level : is-contr (Lehmer O)
  Lehmer-O-level = has-level-in (CanZ , λ { CanZ → idp })

  Lehmer-level : {n : ℕ} → is-set (Lehmer n)
  Lehmer-level {O} = contr-is-set Lehmer-O-level
  Lehmer-level {S n} =
    let ind = LehmerInd {n}
        rec = Lehmer-level {n}
    in  equiv-preserves-level {B = Lehmer (S n)} ind {{×-level Fin-is-set rec}}

Fin≃Lehmer-aux : {n : ℕ} -> Aut (Fin (S n)) ≃ Lehmer n
Fin≃Lehmer-aux {O} =
  Aut (Fin (S O)) ≃⟨ contr-equiv-Unit Aut-level ⟩
  Unit ≃⟨ contr-equiv-Unit Lehmer-O-level ⁻¹ ⟩
  Lehmer O ≃∎
Fin≃Lehmer-aux {S n} =
  Fin (S (S n)) ≃ Fin (S (S n))                              ≃⟨ i ⟩
  Σ (Fin (S (S n))) (λ k → (FinExcept fzero ≃ FinExcept k)) ≃⟨ Σ-cong-equiv-snd ii ⟩
  Fin (S (S n)) × (Fin (S n) ≃ Fin (S n))                    ≃⟨ _ , (×-isemap-r (Fin (S (S n))) (snd (Fin≃Lehmer-aux {n}))) ⟩
  Fin (S (S n)) × Lehmer n                                   ≃⟨ LehmerInd ⟩
  Lehmer (S n) ≃∎

Fin≃Lehmer : {n : ℕ} -> Aut (Fin (S n)) ≃ Lehmer n
Fin≃Lehmer = Fin≃Lehmer-aux ∘e inv-transform-equiv
