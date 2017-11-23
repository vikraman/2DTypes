{-# OPTIONS --without-K --rewriting #-}

module PiFin+.Semantics0 where

open import HoTT

module _ {i j} {X : Type i} {Y : Type j} (e : ⊤ ⊔ X ≃ ⊤ ⊔ Y) where

  reduce-aux : (x : X) →
               Σ (⊤ ⊔ Y) (λ y → –> e (inl tt) == y) →
               Σ (⊤ ⊔ Y) (λ y → –> e (inr x) == y) →
               Y
  reduce-aux x (inl tt , p) (inl tt , q) =
    ⊥-elim (inl≠inr tt x (–>-is-inj e (inl tt) (inr x) (p ∙ ! q)))
  reduce-aux x (inl tt , p) (inr y , q)  = y
  reduce-aux x (inr y  , p) (inl tt , q) = y
  reduce-aux x (inr y  , p) (inr y' , q) = y'

  reduce : X → Y
  reduce x = reduce-aux x (–> e (inl tt) , idp) (–> e (inr x) , idp)

  reduce-aux-β : (x : X) →
                 (w : ⊤ ⊔ Y) → (p : –> e (inl unit) == w) →
                 (v : ⊤ ⊔ Y) → (q : –> e (inr x) == v) →
                 reduce x == reduce-aux x (w , p) (v , q)
  -- cheating by path induction
  reduce-aux-β x w idp v idp = idp

module _ {i j} {X : Type i} {Y : Type j} (e : ⊤ ⊔ X ≃ ⊤ ⊔ Y) where

  -- pattern matches are highlighted in white
  -- slightly different from Robert's proof, why?
  reduce-η-aux : (x : X) →
                 (u : Σ (⊤ ⊔ Y) (λ y → (–> e (inl tt)) == y)) →
                 (v : Σ (⊤ ⊔ Y) (λ y → (–> e (inr x)) == y)) →
                 (Σ (⊤ ⊔ X) (λ y → <– e (inl tt) == y)) →
                 (Σ (⊤ ⊔ X) (λ y → <– e (fst u) == y)) →
                 (Σ (⊤ ⊔ X) (λ y → <– e (fst v) == y)) →
                 reduce (e ⁻¹) (reduce e x) == x
  reduce-η-aux x (inl tt , p) (inl tt , q) _ _ _ =
    ⊥-elim (inr≠inl x tt (! (<–-inv-l e _) ∙ ap (<– e) q ∙ ! (ap (<– e) p) ∙ <–-inv-l e _))
  reduce-η-aux x (u , p) (v , q) _ (inl tt , r) (inl tt , s) =
    ⊥-elim (inr≠inl x tt (! (<–-inv-l e (inr x)) ∙ ap (<– e) q
                         ∙ ap (<– e) (! (<–-inv-r e v) ∙ ap (–> e) s ∙ ! (ap (–> e) r) ∙ <–-inv-r e u)
                         ∙ ! (ap (<– e) p) ∙ <–-inv-l e (inl tt)))
  reduce-η-aux x (inr y , p) (inr y' , q) (inl tt , t) (inl tt , r) (inr x'' , s) =
    ⊥-elim (inr≠inl y tt (! (<–-inv-r e _) ∙ ap (–> e) (r ∙ ! t) ∙ <–-inv-r e _))
  reduce-η-aux x (_ , p) _ _ (inr x' , r) _ =
    ⊥-elim (inr≠inl x' tt (! r ∙ ! (ap (<– e) p) ∙ <–-inv-l e (inl tt)))
  reduce-η-aux x (inr y , p) (inr y' , q) (inr x' , t) (inl tt , r) (inr x'' , s) =
      ap (reduce (e ⁻¹)) (reduce-aux-β e x (inr y) p (inr y') q)
    ∙ reduce-aux-β (e ⁻¹) y' (inr x') t (inr x'') s
    ∙ –> (inr=inr-equiv x'' x) (! s ∙ ap (<– e) (! q) ∙ <–-inv-l e (inr x))
  reduce-η-aux x (inl tt , p) (inr y' , q) _ (inl tt , r) (inr x'' , s) =
      ap (reduce (e ⁻¹)) (reduce-aux-β e x (inl tt) p (inr y') q)
    ∙ reduce-aux-β (e ⁻¹) y' (inl tt) r (inr x'') s
    ∙ –> (inr=inr-equiv x'' x) (! s ∙ ap (<– e) (! q) ∙ <–-inv-l e (inr x))
  reduce-η-aux x (inr y , p) (inl tt , q) _ (inl tt , r) (inr x'' , s) =
      ap (reduce (e ⁻¹)) (reduce-aux-β e x (inr y) p (inl tt) q)
    ∙ reduce-aux-β (e ⁻¹) y (inr x'') s (inl tt) r
    ∙ –> (inr=inr-equiv x'' x) (! s ∙ ap (<– e) (! q ) ∙ <–-inv-l e (inr x))

  reduce-η : (x : X) → reduce (e ⁻¹) (reduce e x) == x
  reduce-η x = reduce-η-aux x (–> e (inl tt) , idp)
                              (–> e (inr x)  , idp)
                              (<– e (inl tt) , idp)
                              (<– e (–> e (inl tt)) , idp)
                              (<– e (–> e (inr x))  , idp)

module _ {i j} {X : Type i} {Y : Type j} (e : ⊤ ⊔ Y ≃ ⊤ ⊔ X) where

  e⁻¹-inv : e ⁻¹ ⁻¹ == e
  e⁻¹-inv = pair= idp (prop-has-all-paths _ _)

  reduce-η' : (x : X) → reduce e (reduce (e ⁻¹) x) == x
  reduce-η' x = ! (ap (λ eq → reduce eq (reduce (e ⁻¹) x)) e⁻¹-inv) ∙ reduce-η (e ⁻¹) x

abstract
  ⊤-⊔-is-inj : ∀ {ℓ} → is-inj (_⊔_ {_} {ℓ} ⊤)
  ⊤-⊔-is-inj X Y p = ua (equiv f g f-g g-f)
    where e : ⊤ ⊔ X ≃ ⊤ ⊔ Y
          e = coe-equiv p
          e' : ⊤ ⊔ Y ≃ ⊤ ⊔ X
          e' = e ⁻¹ -- coe-equiv (! p)
          f : X → Y
          f = reduce e
          g : Y → X
          g = reduce e'
          f-g : (y : Y) → f (g y) == y
          f-g = reduce-η' e
          g-f : (x : X) → g (f x) == x
          g-f = reduce-η e

⊤-cncl : ∀ {ℓ} {X Y : Type ℓ} → ⊤ ⊔ X == ⊤ ⊔ Y → X == Y
⊤-cncl = ⊤-⊔-is-inj _ _
