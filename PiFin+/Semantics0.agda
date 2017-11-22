{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module PiFin+.Semantics0 where

open import HoTT
  -- this is tedious to maintain
  -- using (Type; Type₀; Type₁; lsucc; lmax; lzero;
  --        of-type; -- syntax u :> A
  --        _∘_; is-inj;
  --        ⊥; ⊥-elim;
  --        ⊤; unit;
  --        ℕ; O; S;
  --        _⊔_; inl; inr;
  --        Σ; _,_ ; fst; snd; pair=; fst=; ↓-Σ-in;
  --        Ptd; ⊙[_,_]; pt;
  --        Trunc; [_]; Trunc-elim; Trunc=-equiv;
  --        _==_; idp; !; _∙_; ap; ua; coe; coe-equiv;
  --        PathOver; -- syntax u == v [ B ↓ p ]
  --        _≃_; is-equiv; is-eq; equiv; transport-equiv; –>; <–;
  --        has-level-in; is-contr; is-prop; is-connected;
  --        inhab-prop-is-contr; prop-has-all-paths; prop-has-all-paths-↓;
  --        SubtypeProp; Trunc-level; ℕ₋₂; has-level; transport; Subtype=;
  --        Subtype=-econv; equiv-preserves-level; universe-=-level;
  --        is-set; ⟨-2⟩; is-gpd; ⊔-level; ⟨⟩; _⁻¹;
  --        has-dec-eq; Dec; inr=inr-equiv; dec-eq-is-set;
  --        Subtype=-out; coe-equiv-β; pair==; ua-η; pair=-η;
  --        )

-----------------------------------------------------------------------------
-- A path between ⊤ ⊔ X and ⊤ ⊔ Y induces a path between X and Y
-- Proof is tedious combinatorics

inl!=inr : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
          {a : A} {b : B} → (inl a == inr b) → C
inl!=inr ()

module _ {ℓ} {X Y : Type ℓ}
         (f : ⊤ ⊔ X → ⊤ ⊔ Y) (g : ⊤ ⊔ Y → ⊤ ⊔ X)
         (g-f : (x : ⊤ ⊔ X) → g (f x) == x) where

  finj : {x : X} → (p : f (inl unit) == f (inr x)) → inl unit == inr x
  finj p = ! (g-f (inl unit)) ∙ -- inl unit = g (f (inl unit))
           ap g p ∙             -- g (f (inl unit)) == g (f (inr x))
           (g-f (inr _))        -- g (f (inr x)) = inr x

module _ {ℓ} {X Y : Type ℓ}
         (f : ⊤ ⊔ X → ⊤ ⊔ Y) (g : ⊤ ⊔ Y → ⊤ ⊔ X)
         (f-g : (y : ⊤ ⊔ Y) → f (g y) == y)
         (g-f : (x : ⊤ ⊔ X) → g (f x) == x) where

  reduce-aux : (x : X) →
               Σ (⊤ ⊔ Y) (λ y → f (inl unit) == y) →
               Σ (⊤ ⊔ Y) (λ y → f (inr x) == y) →
               Y
  reduce-aux x (inl unit , p) (inl unit , q) =
    inl!=inr (finj f g g-f (p ∙ ! q))
  reduce-aux x (inl unit , p) (inr y , q)    = y
  reduce-aux x (inr y , p)    (inl unit , q) = y
  reduce-aux x (inr y , p)    (inr y' , q)   = y'

  reduce : X → Y
  reduce x = reduce-aux x (f (inl unit) , idp) (f (inr x) , idp)

  reduce-aux-β : (x : X) →
                 (w : ⊤ ⊔ Y) → (p : f (inl unit) == w) →
                 (v : ⊤ ⊔ Y) → (q : f (inr x) == v) →
                 reduce x == reduce-aux x (w , p) (v , q)
  reduce-aux-β x w p v q =
    ap (λ γ → reduce-aux x γ (f (inr x) , idp)) {!!} ∙
    ap (λ γ → reduce-aux x (w , γ) (f (inr x) , idp)) {!!} ∙
    ap (λ γ → reduce-aux x (w , p) γ) {!!} ∙
    ap (λ γ → reduce-aux x (w , p) (v , γ)) {!!}

{--
   ap (λ γ → rest-aux f g η x γ (f (i₂ x) , refl _))
      (dpair= (p , refl _))
◾ ap (λ γ → rest-aux f g η x (w , γ) (f (i₂ x) , refl _))
      (tpt=l _ p (refl _) ◾ ◾unitl _)
◾ ap (λ γ → rest-aux f g η x (w , p) γ)
      (dpair= (q , (refl _)))
◾ ap (λ γ → rest-aux f g η x (w , p) (v , γ))
      (tpt=l _ q (refl _) ◾ ◾unitl _)
--}

module _ {ℓ} {X Y : Type ℓ}
         (f : ⊤ ⊔ X → ⊤ ⊔ Y) (g : ⊤ ⊔ Y → ⊤ ⊔ X)
         (f-g : (y : ⊤ ⊔ Y) → f (g y) == y)
         (g-f : (x : ⊤ ⊔ X) → g (f x) == x) where

  reduce-η-aux : (x : X) →
                 (u : Σ (⊤ ⊔ Y) (λ y → (f (inl unit)) == y)) →
                 (v : Σ (⊤ ⊔ Y) (λ y → (f (inr x)) == y)) →
                 (Σ (⊤ ⊔ X) (λ y → g (inl unit) == y)) →
                 (Σ (⊤ ⊔ X) (λ y → g (fst u) == y)) →
                 (Σ (⊤ ⊔ X) (λ y → g (fst v) == y)) →
                 reduce g f g-f f-g (reduce f g f-g g-f x) == x
  reduce-η-aux x (inl unit , p) (inl unit , q) _ _ _ =
    inl!=inr (finj f g g-f (p ∙ (! q) ))
  reduce-η-aux x (u , p) (v , q) _ (inl unit , r) (inl unit , s) =
    inl!=inr
      (finj f g g-f
        (p ∙ (! (f-g u) ∙ ap f r ∙ ! (ap f s) ∙ f-g v) ∙ ! q))
  reduce-η-aux x (inr y , p) (inr y' , q) (inl unit , t)
    (inl unit , r) (inr x'' , s) =
    inl!=inr (! (! (f-g _) ∙ ap f (r ∙ ! t) ∙ (f-g _)))
  reduce-η-aux x (_ , p) _ _ (inr _ , r) _ =
    inl!=inr (finj f g g-f (p ∙ ! (f-g _) ∙ ap f r))
  reduce-η-aux x (inr y , p) (inr y' , q) (inr x' , t)
    (inl unit , r) (inr x'' , s) =
    {!!}
  reduce-η-aux x (inl unit , p) (inr y' , q) _
    (inl unit , r) (inr x'' , s) =
    {!!}
  reduce-η-aux x (inr y , p) (inl unit , q) _
    (inl unit , r) (inr x'' , s) =
    {!!}

  reduce-η : (x : X) → reduce g f g-f f-g (reduce f g f-g g-f x) == x
  reduce-η x = reduce-η-aux x
                 (f (inl unit) , idp)
                 (f (inr x) , idp)
                 (g (inl unit) , idp)
                 (g (f (inl unit)) , idp)
                 (g (f (inr x)) , idp)

⊤-cncl : ∀ {ℓ} {X Y : Type ℓ} → ⊤ ⊔ X == ⊤ ⊔ Y → X == Y
⊤-cncl = ua ∘ ⊤-cncl≃ ∘ coe-equiv
  where
    ⊤-cncl≃ : ∀ {ℓ} {X Y : Type ℓ} → (⊤ ⊔ X ≃ ⊤ ⊔ Y) → (X ≃ Y)
    ⊤-cncl≃ (f , record { g = g ; f-g = f-g ; g-f = g-f ; adj = adj }) =
      reduce f g f-g g-f ,
      is-eq
        _
        (reduce g f g-f f-g)
        (reduce-η g f g-f f-g)
        (reduce-η f g f-g g-f)
