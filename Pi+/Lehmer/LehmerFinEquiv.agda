{-# OPTIONS --rewriting --without-K #-}

module Pi+.Lehmer.LehmerFinEquiv where

open import HoTT hiding (_≤_; _<_; ≤-has-all-paths)

open import Pi+.Extra
open import Pi+.Lehmer.FinHelpers
open import Pi+.Lehmer.Lehmer
open import Pi+.Common.InequalityEquiv
open import Pi+.Common.Arithmetic

open import Pi+.UFin.BAut using (Aut)
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

Fin1≃Unit : Fin 1 ≃ Unit
Fin1≃Unit = ⊔₁-Empty ⊤ ∘e Coprod-≃-r Fin-equiv-Empty ∘e Fin-equiv-Coprod

Fin1≃isContr : is-contr (Fin 1 ≃ Fin 1)
Fin1≃isContr = ≃-contr (equiv-preserves-level (Fin1≃Unit ⁻¹)) (equiv-preserves-level (Fin1≃Unit ⁻¹))

Fin≃Lehmer : {n : ℕ} -> Aut (Fin (S n)) ≃ Lehmer n
Fin≃Lehmer {O} = equiv (λ _ → CanZ) (λ CanZ → coe-equiv idp) (λ {CanZ → idp}) λ x → contr-has-all-paths {{Fin1≃isContr}} _ _
Fin≃Lehmer {S n} =
        Fin (S (S n)) ≃ Fin (S (S n))                            ≃⟨ i ⟩
        (Σ[ k ∈ Fin (S (S n)) ] (FinExcept fzero ≃ FinExcept k)) ≃⟨ Σ-cong-equiv-snd ii ⟩
        Fin (S (S n)) × (Fin (S n) ≃ Fin (S n))                  ≃⟨ _ , (×-isemap-r (Fin (S (S n))) (snd (Fin≃Lehmer {n}))) ⟩
        Fin (S (S n)) × Lehmer n                                 ≃⟨ LehmerInd ⟩
        Lehmer (S n) ≃∎
