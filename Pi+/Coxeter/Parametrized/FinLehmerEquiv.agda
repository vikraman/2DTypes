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


Coprod-≃-r-left : {A B C : Type₀} -> (p : A ≃ B) -> (c : C) -> (–> (Coprod-≃-r p) (inr c)) == (inr c)
Coprod-≃-r-left p c = idp

Coprod-≃-r-right : {A B C : Type₀} -> (p : A ≃ B) -> (a : A) -> (–> (Coprod-≃-r {A} {B} {C} p)) (inl a) == inl (–> p a)
Coprod-≃-r-right p a = idp

-- postulate
--     inv-ua : {A B : Type₀} -> (e : A ≃ B) -> ua (e ⁻¹) == ! (ua e)
--     ∘-ua : {A B C : Type₀} -> (e : A ≃ B) -> (f : B ≃ C) -> ua (f ∘e e) == (ua e) ∙ (ua f)
--     id-ua : {A : Type₀} -> ua (ide A) == idp

-- left-inv-id : {A B : Type₀} -> (e : A ≃ B) -> (e ⁻¹) ∘e e == ide A
-- left-inv-id e = {! ua !}

≃-equiv² : {A B : Type₀} -> (A ≃ B) -> ((A ≃ A) ≃ (B ≃ B))
≃-equiv² p = equiv f g f-g g-f
    where
    f : _
    f x = p ∘e x ∘e p ⁻¹
    g : _
    g x = p ⁻¹ ∘e x ∘e p
    f-g : _
    f-g x = TODO
    g-f : _
    g-f x = TODO


Except : {A : Type₀} -> A -> Type₀
Except {A} a = Σ A λ b -> ¬ (a == b)

inj : {A : Type₀} -> {a : A} -> Except a -> A
inj (b , p) = b

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


bottom-lemma : {false : ⊥} -> {A : Type₀} -> {a : A} -> (⊥-elim false == a)
bottom-lemma {()}

unit-except-f : {A : Type₀} -> Σ ((A ⊔ Unit) ≃ (A ⊔ Unit)) (λ e -> –> e (inr tt) == (inr tt)) -> (A ≃ A)
unit-except-f (e , p) = equiv f g f-g g-f
    where

    lemma← : <– e (inr tt) == (inr tt)
    lemma← = ! (! (<–-inv-l e _) ∙ (ap (<– e) p))
    
    f : _
    f a with inspect (–> e (inl a))
    ... | inr x with== bp = 
        let t = (! (<–-inv-l e _)) ∙ (ap (<– e) bp)
        in  ⊥-elim (inr≠inl _ _ (! (t ∙ lemma←)))
    ... | inl b with== bp = b
    g : _
    g a with inspect (<– e (inl a))
    ... | inr tt with== bp = 
        let t = (! (<–-inv-r e _)) ∙ (ap (–> e) bp)
        in  ⊥-elim (inr≠inl _ _ (! (t ∙ p)))
    ... | inl b with== bp = b
    f-g : _
    f-g a with inspect (<– e (inl a)) 
    ... | inr tt with== bp with (inr≠inl _ _ (! ((! (<–-inv-r e _)) ∙ (ap (–> e) bp) ∙ p)))
    f-g a | inr tt with== bp | ()
    f-g a | inl b with== bp with inspect (–> e (inl b))
    ... | inr tt with== ap' = bottom-lemma
    ... | inl a' with== ap' = ! (–> (inl=inl-equiv a a') (! ((ap (–> e) (! bp)) ∙ <–-inv-r e (inl a)) ∙ ap'))

    g-f : _
    g-f a with inspect (–> e (inl a)) 
    ... | inr tt with== bp with (inr≠inl _ _ (! ((! (<–-inv-l e _)) ∙ (ap (<– e) bp) ∙ lemma←)))
    g-f a | inr tt with== bp | ()
    g-f a | inl b with== bp with inspect (<– e (inl b))
    ... | inr tt with== ap' = bottom-lemma
    ... | inl a' with== ap' = ! (–> (inl=inl-equiv a a') (! (ap (<– e) (! bp) ∙ (<–-inv-l e (inl a))) ∙ ap'))

unit-except : {A : Type₀} -> is-equiv (unit-except-f {A})
unit-except = is-eq unit-except-f g f-g g-f
    where
    g : _
    g x = Coprod-≃-r x , Coprod-≃-r-left x tt
    f-g : _
    f-g x = pair= idp (↓-cst-in {!  !})
    g-f : _
    g-f x = pair= {!   !} {!   !}

lemma2 : {A : Type₀} -> (has-dec-eq A) -> (e : (A ⊔ Unit) ≃ (A ⊔ Unit)) ->
        (a : A) -> (–> e (inr tt) == (inl a)) -> 
        (c : Except a) -> (–> e (inl (inj c)) == (inr tt)) ->
        ((Except {Except a} c) ⊔ Unit ⊔ Unit) ≃ ((Except {Except a} c) ⊔ Unit ⊔ Unit)
lemma2 deq e a ax c cx = {!   !}

lemma : {A : Type₀} -> (has-dec-eq A) -> (e : (A ⊔ Unit) ≃ (A ⊔ Unit)) 
        -> (a : A) -> (–> e (inr tt) == (inl a)) -> (Except a ⊔ Unit) ≃ (Except a ⊔ Unit)
lemma {A} deq e a ax =
    let a→tt : –> e (inl a) == (inr tt) 
        a→tt = {!   !}
    in  equiv f g f-g g-f
        where    
        f : _
        f (inl (x , x≠a)) with (inspect (–> e (inl x)))
        ... | inl b with== bp = inl (b , (λ pp → 
            let ll = ap inl (! pp)

            in  inr≠inl _ _ (({!   !} ∙ bp) ∙ ll)))
        ... | inr tt with== bp = inl {!   !}
        f (inr tt) = inr tt
        g : _
        g x = {!   !}
        f-g : _
        f-g x = {!   !}
        g-f : _
        g-f x = {!   !}
    

aut-⊔ : {A : Type₀} -> (has-dec-eq A) -> ((A ⊔ Unit) ≃ (A ⊔ Unit)) -> ((A ⊔ Unit) × (A ≃ A))
aut-⊔ deq e with inspect (–> e (inr tt))
... | inl a with== ax = 
    let e-except = Except≃ deq a
    in  (inl a) , –> (≃-equiv² e-except) (lemma deq e a ax)
... | inr tt with== bx = (inr tt) , –> (unit-except-f , unit-except) (e , bx)


aut-⊔-≃ : {A : Type₀} -> (deq : has-dec-eq A) -> is-equiv (aut-⊔ deq)
aut-⊔-≃ deq = is-eq (aut-⊔ deq) g f-g g-f
    where
    g : _
    g (inl x , e) = 
        let e-except₁ = Except≃ deq x ⁻¹
        in  {!   !} 
    g (inr tt , e) = Coprod-≃-r e
    f-g : _
    f-g x = {!   !}
    g-f : _
    g-f x = {!   !}

Fin1≃Unit : Fin 1 ≃ Unit
Fin1≃Unit = ⊔₁-Empty ⊤ ∘e Coprod-≃-r Fin-equiv-Empty ∘e Fin-equiv-Coprod

Fin1≃isContr : is-contr (Fin 1 ≃ Fin 1)
Fin1≃isContr = ≃-contr (equiv-preserves-level (Fin1≃Unit ⁻¹)) (equiv-preserves-level (Fin1≃Unit ⁻¹))

Fin≃Lehmer : {n : ℕ} -> (Fin (S n) ≃ Fin (S n)) ≃ Lehmer n
Fin≃Lehmer {O} = equiv (λ _ → CanZ) (λ CanZ → coe-equiv idp) (λ {CanZ → idp}) λ x → contr-has-all-paths {{Fin1≃isContr}} _ _
Fin≃Lehmer {S n} =
        Fin (S (S n)) ≃ Fin (S (S n))                   ≃⟨ ≃-equiv² Fin-equiv-Coprod ⟩
        ((Fin (S n) ⊔ Unit) ≃ (Fin (S n) ⊔ Unit))       ≃⟨ ? ⟩
        ((Fin (S n) ⊔ Unit) × (Fin (S n) ≃ Fin (S n)))  ≃⟨ ((_ , ×-isemap-l _ (snd (Fin-equiv-Coprod ⁻¹)))) ⟩
        Fin (S (S n)) × (Fin (S n) ≃ Fin (S n))         ≃⟨ _ , (×-isemap-r _ (snd (Fin≃Lehmer {n}))) ⟩
        Fin (S (S n)) × Lehmer n                        ≃⟨ LehmerInd ⟩
        Lehmer (S n) ≃∎