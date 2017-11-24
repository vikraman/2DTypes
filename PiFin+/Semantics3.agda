{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module PiFin+.Semantics3 where

open import HoTT
open import PiFin+.Semantics0
open import PiFin+.Semantics1
open import PiFin+.Semantics2

module _ {a b} {A : Type a} {B : A → Type b} where

  data Graph (f : (x : A) → B x) (x : A) (y : B x) : Type b where
    path : f x == y → Graph f x y

  inspect : (f : (x : A) → B x) (x : A) → Graph f x (f x)
  inspect _ _ = path idp

inl-El : {n : ℕ} → El (S n)
inl-El = inl tt

inr-El : (m : ℕ) → {n : ℕ} → El (S n)
inr-El O {n} = inl tt
inr-El (S m) {O} = inl tt
inr-El (S m) {S n} = inr (inr-El m {n})

coe-id-ide : ∀ {ℓ} {X : Type ℓ}
           → (e : X ≃ X) (α : (x : X) → –> e x == x)
           → e == ide X
coe-id-ide e α = pair= (λ= α) prop-has-all-paths-↓

coe-id-idp : ∀ {ℓ} {X : Type ℓ}
           → (p : X == X) (α : (x : X) → coe p x == x)
           → p == idp
coe-id-idp p α = ! (ua-η p)
               ∙ ap ua (coe-id-ide (coe-equiv p) α)
               ∙ ua-η idp

-- generalize to inl-El and inr-El
ψ : {n : ℕ} (e : El (S (S n)) ≃ El (S (S n)))
  → ¬ (Σ (El (S (S n))) (λ x → (–> e (inl tt) == x) × (–> e (inr (inl tt)) == x)))
ψ e (x , p , q) = inl≠inr tt (inl tt) (–>-is-inj e (inl tt) (inr (inl tt)) (p ∙ ! q))

all-1-paths-O : (p : El O == El O) → p == idp
all-1-paths-O p = prop-has-all-paths p idp

instance
  ElSO-is-prop : is-prop (El (S O))
  ElSO-is-prop =
    has-level-in λ { (inl tt) (inl tt) → has-level-in (idp , (λ { idp → idp }))
                   ; (inl tt) (inr ()) ; (inr ()) _ }

all-1-paths-SO : (p : El (S O) == El (S O)) → p == idp
all-1-paths-SO p = prop-has-all-paths p idp

-- `swap₊-coe-β
coe-swap-swap-El2 : (p : El 2 == El 2)
                  → (α : coe p (inl tt) == inr (inl tt))
                  → (β : coe p (inr (inl tt)) == inl tt)
                  → p == `swap₊ 1 1
coe-swap-swap-El2 p α β = {!!}

all-1-paths-SSO : (p : El (S (S O)) == El (S (S O)))
                → (p == idp) ⊔ (p == `swap₊ 1 1)
all-1-paths-SSO p with coe p (inl tt)       | inspect (coe p) (inl tt)
                     | coe p (inr (inl tt)) | inspect (coe p) (inr (inl tt))
... | inl tt       | path r | inl tt       | path s = ⊥-elim (ψ (coe-equiv p) (inl tt , r , s))
... | inl tt       | path r | inr (inl tt) | path s = inl (coe-id-idp p λ { (inl tt) → r ; (inr (inl tt)) → s ; (inr (inr ())) })
... | inr (inl tt) | path r | inl tt       | path s = inr (coe-swap-swap-El2 p r s)
... | inr (inl tt) | path r | inr (inl tt) | path s = ⊥-elim (ψ (coe-equiv p) (inr (inl tt) , r , s))
... | inr (inr ()) | path r | _            | _
... | _            | path r | inr (inr ()) | _
