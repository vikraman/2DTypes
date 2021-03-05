{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances --allow-unsolved-metas #-}

module Pi+.Indexed.Equiv2Norm where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.UFin
open import Pi+.Extra
open import Pi+.UFin.BAut

open import Pi+.Indexed.Equiv0Norm
open import Pi+.Indexed.Equiv1Norm

open import Pi+.Indexed.Equiv1NormHelpers using (pi^2list; pi^2list-!^-β)
open import Pi+.Lehmer.LehmerFinEquiv using (Fin≃Lehmer)
open import Pi+.Coxeter.LehmerCoxeterEquiv using (immersion⁻¹; immersion⁻¹-respects≈)
open import Pi+.Coxeter.Sn using (≈-inv-l; ≈-inv-r)
open import HoTT

private
    variable
        n m : ℕ

abstract
  e= : ∀ {i} {X : Type i} {e₁ e₂ : Fin n ≃ X} → ((f : Fin n) → (–> e₁ f == –> e₂ f)) → e₁ == e₂
  e= h = pair= (λ= h) prop-has-all-paths-↓

abstract
  loop-η : ∀ {i} {X : Type i} {{_ : is-set X}} {x : X} → (p : x == x) → p == idp
  loop-η p = prop-has-all-paths p idp

abstract
  uip : ∀ {i} {X : Type i} {{_ : is-set X}} {x y : X} → (p q : x == y) → p == q
  uip p q = prop-has-all-paths p q

module _ {c₁ c₂ : O ⟷₁^ m} where

  evalNorm₂-O : c₁ ⟷₂^ c₂ → evalNorm₁ c₁ == evalNorm₁ c₂
  evalNorm₂-O α = e= λ { (n , ()) }

evalNorm₂-S : {c₁ c₂ : S n ⟷₁^ S m} → c₁ ⟷₂^ c₂ → evalNorm₁ c₁ == evalNorm₁ c₂
evalNorm₂-S (assoc◎l^ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}) with (⟷₁^-eq-size (c₁ ◎^ c₂ ◎^ c₃))
... | idp with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂) | (⟷₁^-eq-size c₃)
... | idp | idp | p rewrite loop-η p = ap (<– Fin≃Lehmer ∘ immersion⁻¹) (! (++-assoc (pi^2list c₁) (pi^2list c₂) (pi^2list c₃)))
evalNorm₂-S (assoc◎r^ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}) with (⟷₁^-eq-size (c₁ ◎^ c₂ ◎^ c₃))
... | idp with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂) | (⟷₁^-eq-size c₃)
... | idp | idp | p rewrite loop-η p = ap (<– Fin≃Lehmer ∘ immersion⁻¹) (++-assoc (pi^2list c₁) (pi^2list c₂) (pi^2list c₃))
evalNorm₂-S {c₁ = c₁} {c₂ = c₂} idl◎l^ with (⟷₁^-eq-size c₂)
... | idp = idp
evalNorm₂-S {c₁ = c₁} {c₂ = c₂} idl◎r^ with (⟷₁^-eq-size c₁)
... | idp = idp
evalNorm₂-S {c₁ = c₁} {c₂ = c₂} idr◎l^ with (⟷₁^-eq-size c₂)
... | idp = ap (<– Fin≃Lehmer ∘ immersion⁻¹) (++-unit-r (pi^2list c₂))
evalNorm₂-S {c₁ = c₁} {c₂ = c₂} idr◎r^ with (⟷₁^-eq-size c₂)
... | idp = ap (<– Fin≃Lehmer ∘ immersion⁻¹) (! (++-unit-r (pi^2list c₁)))
evalNorm₂-S (linv◎l^ {c = c}) with (⟷₁^-eq-size c)
... | idp =
  let r = (immersion⁻¹-respects≈ {_} {pi^2list c ++ reverse (pi^2list c)} {nil} (≈-inv-r (pi^2list c)))
  in  ap (<– Fin≃Lehmer) (ap immersion⁻¹ (ap (λ e → pi^2list c ++ e) (pi^2list-!^-β c)) ∙ r)
evalNorm₂-S (linv◎r^ {c = c}) with (⟷₁^-eq-size c)
... | idp =
  -- why can't I use the above case?
  let r = (immersion⁻¹-respects≈ {_} {pi^2list c ++ reverse (pi^2list c)} {nil} (≈-inv-r (pi^2list c)))
  in  ! (ap (<– Fin≃Lehmer) (ap immersion⁻¹ (ap (λ e → pi^2list c ++ e) (pi^2list-!^-β c)) ∙ r))
evalNorm₂-S (rinv◎l^ {c = c}) with (⟷₁^-eq-size c)
... | idp =
  let r = (immersion⁻¹-respects≈ {_} {reverse (pi^2list c) ++ pi^2list c} {nil} (≈-inv-l (pi^2list c)))
  in  (ap (<– Fin≃Lehmer) (ap immersion⁻¹ (ap (λ e → e ++ pi^2list c) (pi^2list-!^-β c)) ∙ r))
evalNorm₂-S (rinv◎r^ {c = c}) with (⟷₁^-eq-size c)
... | idp =
  -- why can't I use the above case?
  let r = (immersion⁻¹-respects≈ {_} {reverse (pi^2list c) ++ pi^2list c} {nil} (≈-inv-l (pi^2list c)))
  in  ! (ap (<– Fin≃Lehmer) (ap immersion⁻¹ (ap (λ e → e ++ pi^2list c) (pi^2list-!^-β c)) ∙ r))
evalNorm₂-S id⟷₂^ = idp
evalNorm₂-S {c₁ = c₁} {c₂ = c₂} (_■^_ α₁ α₂) with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂)
... | idp | q rewrite loop-η q =
  let r₁ = evalNorm₂-S α₁
      r₂ = evalNorm₂-S α₂
  in  r₁ ∙ r₂
evalNorm₂-S (_⊡^_ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃} {c₄ = c₄} α_₁ α₂) with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂) | (⟷₁^-eq-size c₃) | (⟷₁^-eq-size c₄)
... | idp | idp | p | q rewrite loop-η p rewrite loop-η q = TODO!
evalNorm₂-S (⊕id⟷₁⟷₂^ {n = O}) = idp
evalNorm₂-S (⊕id⟷₁⟷₂^ {n = S n}) = e= λ { (O , p) → idp ; (S n , p) → TODO! }
evalNorm₂-S (!⊕id⟷₁⟷₂^ {n = O}) = idp
evalNorm₂-S (!⊕id⟷₁⟷₂^ {n = S n}) = e= λ { (O , p) → idp ; (S n , p) → TODO! }
evalNorm₂-S hom◎⊕⟷₂^ = TODO!
evalNorm₂-S (resp⊕⟷₂ {n = O} {c₁ = c₁} {c₂ = c₂} α) with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂)
... | idp | idp = idp
evalNorm₂-S (resp⊕⟷₂ {n = S n} {c₁ = c₁} {c₂ = c₂} α) with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂)
... | idp | q rewrite loop-η q = TODO!
evalNorm₂-S (hom⊕◎⟷₂^ {c₁ = c₁} {c₂ = c₂}) with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂)
... | idp | idp = TODO!
evalNorm₂-S (swapr₊⟷₂^ {n = O}) = e= λ { (O , p) → idp ; (S n , p) → TODO! }
evalNorm₂-S (swapr₊⟷₂^ {n = S n}) = e= λ { (O , p) → TODO! ; (S n , p) → TODO! }
evalNorm₂-S (swapl₊⟷₂^ {n = O}) = e= λ { (O , p) → idp ; (S n , p) → TODO! }
evalNorm₂-S (swapl₊⟷₂^ {n = S n}) = e= λ { (O , p) → TODO! ; (S n , p) → TODO! }
evalNorm₂-S (hexagonl₊l {n = O}) = e= λ { (O , p) → idp ; (S n , p) → idp }
evalNorm₂-S (hexagonl₊l {n = S n}) = e= λ { (O , p) → idp ; (S n , p) → idp }
evalNorm₂-S (hexagonl₊r {n = O}) = e= λ { (O , p) → idp ; (S n , p) → idp }
evalNorm₂-S (hexagonl₊r {n = S n}) = e= λ { (O , p) → idp ; (S n , p) → idp }

evalNorm₂ : {c₁ c₂ : n ⟷₁^ m} → c₁ ⟷₂^ c₂ → evalNorm₁ c₁ == evalNorm₁ c₂
evalNorm₂ {n = O} = evalNorm₂-O
evalNorm₂ {n = S n} {c₁ = c₁} with (⟷₁^-eq-size c₁)
... | idp = evalNorm₂-S

_ : {n : ℕ} → evalNorm₁ (id⟷₁^ {n = n}) == evalNorm₁ (id⟷₁^ {n = n})
_ = e= (λ { (O , p) → idp ; (S n , p) → idp })

_ : evalNorm₁ (swap₊^ {n = n} ◎^ swap₊^ {n = n}) == evalNorm₁ id⟷₁^
_ = e= (λ { (O , p) → idp ; (S n , p) → idp })
