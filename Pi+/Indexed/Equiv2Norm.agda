{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances --allow-unsolved-metas #-}

module Pi+.Indexed.Equiv2Norm where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.UFin
open import Pi+.Extra
open import Pi+.UFin.BAut

open import Pi+.Indexed.Equiv0Norm
open import Pi+.Indexed.Equiv1Norm

open import Pi+.Indexed.Equiv1NormHelpers using (norm2list)
open import Pi+.Lehmer.LehmerFinEquiv using (Fin≃Lehmer)
open import Pi+.Coxeter.LehmerCoxeterEquiv using (immersion⁻¹)

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

module _ {c₁ c₂ : O ⟷₁^ m} where

  evalNorm₂-O : c₁ ⟷₂^ c₂ → evalNorm₁ c₁ == evalNorm₁ c₂
  evalNorm₂-O α = e= λ { (n , ()) }

module _ {c₁ c₂ : S n ⟷₁^ m} where

  evalNorm₂-S : c₁ ⟷₂^ c₂ → evalNorm₁ c₁ == evalNorm₁ c₂
  evalNorm₂-S (assoc◎l^ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}) with (⟷₁^-eq-size (c₁ ◎^ c₂ ◎^ c₃))
  ... | idp with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂) | (⟷₁^-eq-size c₃)
  ... | idp | idp | p rewrite loop-η p = ap (<– Fin≃Lehmer ∘ immersion⁻¹) (! (++-assoc (norm2list c₁) (norm2list c₂) (norm2list c₃)))
  evalNorm₂-S (assoc◎r^ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}) with (⟷₁^-eq-size (c₁ ◎^ c₂ ◎^ c₃))
  ... | idp with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂) | (⟷₁^-eq-size c₃)
  ... | idp | idp | p rewrite loop-η p = ap (<– Fin≃Lehmer ∘ immersion⁻¹) (++-assoc (norm2list c₁) (norm2list c₂) (norm2list c₃))
  evalNorm₂-S idl◎l^ with (⟷₁^-eq-size c₂)
  ... | idp = idp
  evalNorm₂-S idl◎r^ with (⟷₁^-eq-size c₁)
  ... | idp = idp
  evalNorm₂-S idr◎l^ with (⟷₁^-eq-size c₂)
  ... | idp = ap (<– Fin≃Lehmer ∘ immersion⁻¹) (++-unit-r (norm2list c₂))
  evalNorm₂-S idr◎r^ with (⟷₁^-eq-size c₂)
  ... | idp = ap (<– Fin≃Lehmer ∘ immersion⁻¹) (! (++-unit-r (norm2list c₁)))
  evalNorm₂-S (linv◎l^ {c = c}) with (⟷₁^-eq-size c)
  ... | idp = TODO
  evalNorm₂-S (linv◎r^ {c = c}) with (⟷₁^-eq-size c)
  ... | idp = TODO
  evalNorm₂-S (rinv◎l^ {c = c}) with (⟷₁^-eq-size c)
  ... | idp = TODO
  evalNorm₂-S (rinv◎r^ {c = c}) with (⟷₁^-eq-size c)
  ... | idp = TODO
  evalNorm₂-S id⟷₂^ = idp
  evalNorm₂-S (trans⟷₂^ α₁ α₂) with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂)
  ... | idp | q rewrite loop-η q = TODO
  evalNorm₂-S (_⊡^_ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃} {c₄ = c₄} α_₁ α₂) with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂) | (⟷₁^-eq-size c₃) | (⟷₁^-eq-size c₄)
  ... | idp | idp | p | q rewrite loop-η p rewrite loop-η q = TODO
  evalNorm₂-S (⊕id⟷₁⟷₂^ {n = O}) = idp
  evalNorm₂-S (⊕id⟷₁⟷₂^ {n = S n}) = e= λ { (O , p) → idp ; (S n , p) → TODO }
  evalNorm₂-S (!⊕id⟷₁⟷₂^ {n = O}) = idp
  evalNorm₂-S (!⊕id⟷₁⟷₂^ {n = S n}) = e= λ { (O , p) → idp ; (S n , p) → TODO }
  evalNorm₂-S hom◎⊕⟷₂^ = TODO
  evalNorm₂-S (resp⊕⟷₂ {c₁ = c₁} {c₂ = c₂} α) with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂)
  ... | idp | q rewrite loop-η q = TODO
  evalNorm₂-S (hom⊕◎⟷₂^ {c₁ = c₁} {c₂ = c₂}) with (⟷₁^-eq-size c₁) | (⟷₁^-eq-size c₂)
  ... | idp | idp = TODO
  evalNorm₂-S (swapr₊⟷₂^ {n = O}) = e= λ { (O , p) → idp ; (S n , p) → TODO }
  evalNorm₂-S (swapr₊⟷₂^ {n = S n}) = e= λ { (O , p) → TODO ; (S n , p) → TODO }
  evalNorm₂-S (swapl₊⟷₂^ {n = O}) = e= λ { (O , p) → idp ; (S n , p) → TODO }
  evalNorm₂-S (swapl₊⟷₂^ {n = S n}) = e= λ { (O , p) → TODO ; (S n , p) → TODO }

evalNorm₂ : {c₁ c₂ : n ⟷₁^ m} → c₁ ⟷₂^ c₂ → evalNorm₁ c₁ == evalNorm₁ c₂
evalNorm₂ {n = O} = evalNorm₂-O
evalNorm₂ {n = S n} = evalNorm₂-S

_ : {n : ℕ} → evalNorm₁ (id⟷₁^ {n = n}) == evalNorm₁ (id⟷₁^ {n = n})
_ = e= (λ { (O , p) → idp ; (S n , p) → idp })

_ : evalNorm₁ (swap₊^ {n = n} ◎^ swap₊^ {n = n}) == evalNorm₁ id⟷₁^
_ = e= (λ { (O , p) → idp ; (S n , p) → idp })
