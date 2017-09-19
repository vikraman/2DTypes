{-# OPTIONS --without-K --rewriting #-}

module PiFin.EMSpace where

open import UnivalentTypeTheory
open import PropositionalTruncation
open import RewriteRelation
--import TwoUniverse as U

1types : ∀ ℓ → Type (lsuc ℓ)
1types ℓ = Σ (Type ℓ) (λ T → has-lvl T lvl-1)

data PathOver {ℓ} {ℓ'} {A : Type ℓ} (P : A → Type ℓ') : {x y : A} (p : x == y) (ux : P x) (uy : P y) → Type (ℓ ⊔ ℓ') where
  reflp : ∀ {x : A} (ux : P x) → PathOver P (refl x) ux ux

module _ {ℓ} {ℓ'} {A : Type ℓ} {P : A → Type ℓ'} {x y : A} {p : x == y} (ux : P x) {uy : P y} where
  g : tpt P p ux == uy → PathOver P p ux uy
  g (refl ux) = {!!}

{-
module _ {ℓ} {ℓ'} {A : Type ℓ} {P : A → Type ℓ'} {x y z : A} {p : x == y} {q : y == z} {ux : P x} {uy : P y} where
  _p◾_ : PathOver P p ux uy → PathOver P q ux uy → PathOver P (p ◾ q) ux uy
  (reflp ux) p◾ (reflp .ux) = {!!}
-}

{-
module _ {ℓ} {ℓ'} {A : Type ℓ} {P : A → Type ℓ'} {x y : A} {p : x == y} (ux : P x) {uy : P y} where
  path-over-eq-tpt : PathOver P p ux uy ≃ (∀ {uy : P x} → tpt P p ux == uy)
  path-over-eq-tpt = (λ { (reflp ux) → refl ux }) ,
    {!!} --qinv-is-equiv (ind= {X = P y} (λ {uy1} {uy2} uy → PathOver P p {!!} {!!}) {!!} {!!} , {!!} , {!!})
-}

--PathOver : ∀ {ℓ} {ℓ'} {A : Type ℓ} (P : A → Type ℓ') {x y : A} (p : x == y) (ux : P x) (uy : P y) → Type ℓ'
--PathOver P p ux uy = tpt P p ux == uy

postulate
  K : Type₀
  base : K
  loop : base == base
  ρ : loop ◾ loop == refl base
  φ : has-lvl K lvl-1

module Ind-K {ℓ} (P    : K → 1types ℓ)
                 (base* : p₁ (P base))
                 (loop* : PathOver (p₁ ∘ P) loop base* base*)
                 (ρ*    : PathOver (λ p → PathOver (p₁ ∘ P) p base* base*) ρ {!!} {!!}) where
  postulate
    f : (x : K) → p₁ (P x)
    base-β : f base ↦ base*
  {-# REWRITE base-β #-}

  --postulate
    --loop-β : apd  (p₁ ∘ P) f loop == loop*
    --ρ-β    : apd₂ (λ x → tpt {!!} {!!} {!!}) f ρ    == ρ*


module Rec-K {ℓ} (C : 1types ℓ) (base* : p₁ C) (loop* : base* == base*) (ρ* : loop* == loop*) where
  postulate
    f : K → p₁ C
    base-β : f base ↦ base*
  {-# REWRITE base-β #-}

  postulate
    loop-β : ap f loop == loop*
    ρ-β    : ap (λ _ → loop*) ρ == ρ*

{-
_ : K ≃ U.`𝟚
_ = f , qinv-is-equiv (g , Ind-K.f (λ z → (g (f z) == z) , {!!}) {!!} {!!} , {!!}) where

  f : K → U𝟚
  f = Rec-K.f (U𝟚 , {!!}) `𝟚 U.`not --TODO: RHO

  g : U𝟚 → K
  g (_ , r) = recTrunc K (λ _ → base) (lvl-1-is-prop φ) r
-}
