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
open import lib.types.Nat using (<-has-all-paths; ltS)

open import Pi+.Coxeter.Common.Lehmer
open import Pi+.Coxeter.Common.InequalityEquiv
open import Pi+.Coxeter.Common.Arithmetic

open import Pi+.UFin.Monoidal
open import Pi+.Extra
open import Pi+.Misc

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
Coprod-≃-r = TODO

Coprod-≃-l : {A B C : Type₀} -> (A ≃ B) -> (C ⊔ A) ≃ (C ⊔ B)
Coprod-≃-l e = equiv f g f-g g-f
    where
    f : _
    f (inl x) = inl x
    f (inr x) = inr (–> e x)
    g : _
    g (inl x) = inl x
    g (inr x) = inr (<– e x)
    f-g : _
    f-g (inl x) = idp
    f-g (inr x) = ap inr (<–-inv-r e x)
    g-f : _
    g-f (inl x) = idp
    g-f (inr x) = ap inr (<–-inv-l e x)

Coprod-≃-l-left : {A B C : Type₀} -> (p : A ≃ B) -> (c : C) -> (–> (Coprod-≃-l p) (inl c)) == (inl c)
Coprod-≃-l-left p c = idp

≃-equiv : {A B : Type₀} -> (A ≃ B) -> ((A ≃ A) ≃ (B ≃ B))
≃-equiv p = TODO

Except : {A : Type₀} -> A -> Type₀
Except {A} a = Σ A λ b -> ¬ (a == b)

Except≃ : {A : Type₀} -> (has-dec-eq A) -> (a : A) -> (Except a) ⊔ Unit ≃ A
Except≃ deq a = equiv f g f-g g-f
    where 
    f : _
    f (inl (x , p)) = x
    f (inr tt) = a
    g : _
    g b with deq a b
    ... | inl _ = inr tt
    ... | inr x = inl (b , x)
    f-g : _
    f-g b with deq a b
    ... | inl p = p
    ... | inr x = idp
    g-f : _
    g-f (inl (b , p)) with deq a b
    ... | inl idp = ⊥-elim {_} {λ x → _ == inl (b , p)} (p idp)
    ... | inr x = ap inl (pair= idp {!  !})
    g-f (inr tt) with deq a a
    ... | inl x = idp
    ... | inr q with (q idp) -- Agda complains when using ⊥-elim...
    ... | ()


lemma-f : {A : Type₀} -> Σ ((Unit ⊔ A) ≃ (Unit ⊔ A)) (λ e -> –> e (inl tt) == (inl tt)) -> (A ≃ A)
lemma-f (e , p) = equiv f g f-g g-f
    where

    lemma← : <– e (inl tt) == (inl tt)
    lemma← = ! (! (<–-inv-l e _) ∙ (ap (<– e) p))
    
    f : _
    f a with inspect (–> e (inr a))
    ... | inl x with== bp = 
        let t = (! (<–-inv-l e _)) ∙ (ap (<– e) bp)
        in  ⊥-elim (inl≠inr _ _ (! (t ∙ lemma←)))
    ... | inr b with== bp = b
    g : _
    g a with inspect (<– e (inr a))
    ... | inl tt with== bp = 
        let t = (! (<–-inv-r e _)) ∙ (ap (–> e) bp)
        in  ⊥-elim (inl≠inr _ _ (! (t ∙ p)))
    ... | inr b with== bp = b
    f-g : _
    f-g a = {!   !}
    g-f : _
    g-f a = {!   !}

lemma : {A : Type₀} -> is-equiv (lemma-f {A})
lemma = is-eq lemma-f g f-g g-f
    where
    g : _
    g x = Coprod-≃-l x , Coprod-≃-l-left x tt
    f-g : _
    f-g x = pair= idp (↓-cst-in {!  !})
    g-f : _
    g-f x = pair= {!   !} {!   !}

-- symmetric version of the lemma above
lemma-r : {A : Type₀} -> Σ ((A ⊔ Unit) ≃ (A ⊔ Unit)) (λ e -> –> e (inr tt) == (inr tt)) ≃ (A ≃ A)
lemma-r = TODO

aut-⊔ : {A : Type₀} -> ((A ⊔ Unit) ≃ (A ⊔ Unit)) -> ((A ⊔ Unit) × (A ≃ A))
aut-⊔ e with inspect (–> e (inr tt))
... | inl x with== bx = (inl x) , {!   !}
... | inr tt with== bx = (inr tt) , –> lemma-r (e , bx)

aut-⊔-≃ : {A : Type₀} -> is-equiv (aut-⊔ {A})
aut-⊔-≃ = is-eq aut-⊔ {!   !} {!   !} {!   !}

Fin1≃Unit : Fin 1 ≃ Unit
Fin1≃Unit = ⊔₁-Empty ⊤ ∘e Coprod-≃-r Fin-equiv-Empty ∘e Fin-equiv-Coprod

Fin1≃isContr : is-contr (Fin 1 ≃ Fin 1)
Fin1≃isContr = ≃-contr (equiv-preserves-level (Fin1≃Unit ⁻¹)) (equiv-preserves-level (Fin1≃Unit ⁻¹))

Fin≃Lehmer : {n : ℕ} -> (Fin (S n) ≃ Fin (S n)) ≃ Lehmer n
Fin≃Lehmer {O} = equiv (λ _ → CanZ) (λ CanZ → coe-equiv idp) (λ {CanZ → idp}) λ x → contr-has-all-paths {{Fin1≃isContr}} _ _
Fin≃Lehmer {S n} =
        Fin (S (S n)) ≃ Fin (S (S n))                   ≃⟨ ≃-equiv Fin-equiv-Coprod ⟩
        ((Fin (S n) ⊔ Unit) ≃ (Fin (S n) ⊔ Unit))       ≃⟨ _ , aut-⊔-≃ ⟩
        ((Fin (S n) ⊔ Unit) × (Fin (S n) ≃ Fin (S n)))  ≃⟨ ((_ , ×-isemap-l _ (snd (Fin-equiv-Coprod ⁻¹)))) ⟩
        Fin (S (S n)) × (Fin (S n) ≃ Fin (S n))         ≃⟨ _ , (×-isemap-r _ (snd (Fin≃Lehmer {n}))) ⟩
        Fin (S (S n)) × Lehmer n                        ≃⟨ LehmerInd ⟩
        Lehmer (S n) ≃∎