{-# OPTIONS --rewriting #-}

module Pi+.Copy where

open import lib.Base
open import lib.NType
open import lib.NType2
-- open import lib.Equivalence
open import lib.Univalence
open import lib.PathGroupoid
open import lib.PathOver
open import lib.types.Fin
open import lib.types.List
open import lib.types.Sigma
open import lib.types.Coproduct
open import lib.types.Unit
open import lib.types.Nat using (<-has-all-paths; ltS)
 
------------------------------------------------------------------------------
-- This is WAY simpler than using 'with' and 'inspect'!

record isqinv {A B : Type₀} (f : A → B) : Type₀ where
  constructor qinv
  field
    g : B → A
    α : ∀ a -> f (g a) == a
    β : ∀ b -> g (f b) == b

_≃_ : Type₀ -> Type₀ -> Type₀
A ≃ B = Σ (A → B) isqinv

inj≃ : {A B : Type₀} → (eq : A ≃ B) → (x y : A) → (fst eq x == fst eq y → x == y)
inj≃ (f , qinv g α β) x y p = ! (β x) ∙ ap g p ∙ β y

sym≃ : {A B : Type₀} → (A ≃ B) → B ≃ A
sym≃ (A→B , equiv) = e.g , qinv A→B e.β e.α
  where module e = isqinv equiv


record Ev {A B : Type₀} (f : A → B) (x : A) : Type₀ where
  constructor ev
  field
    v : B
    fx=v : f x == v
 
mkV : {A B : Type₀} → (f : A → B) → (x : A) → Ev f x
mkV f x = ev (f x) idp

private
  bad-path : {A B : Type₀} → (a : A) → (b : B) → inl a == inr b → ⊥
  bad-path x y ()

------------------------------------------------------------------------------
-- Very complex proof that we can cancel units on the left of ⊔

-- Some repeated patterns:

inj₁≡ : {A B : Type₀} → {a b : A} → inl {A = A} {B} a == inl b → a == b
inj₁≡ idp = idp

inj₂≡ : {A B : Type₀} → {a b : B} → inr {A = A} {B} a == inr b → a == b
inj₂≡ idp = idp

-- use injectivity of equivalences to go from f x == f y to x == y

injectivity : {A B : Type₀} (equiv : (⊤ ⊔ A) ≃ (⊤ ⊔ B)) →
  (a : A) → fst equiv (inl tt) == fst equiv (inr a) → (inl tt == inr a) 
injectivity equiv x path = inj≃ equiv (inl tt) (inr x) path

left-cancel-⊤ : {A B : Type₀} →  ((⊤ ⊔ A) ≃ (⊤ ⊔ B)) → A ≃ B
left-cancel-⊤ {A} {B} (f₁ , qinv g₁ α₁ β₁) =
  let eqv = (f₁ , qinv g₁ α₁ β₁) in
  let v₁ = mkV f₁ (inl tt) in
  let v₂ = mkV g₁ (inl tt) in
  mk₁ {A} {B} eqv v₁ v₂
  where
    mk₁ : {A B : Type₀} (e : (⊤ ⊔ A) ≃ (⊤ ⊔ B)) → 
              let (f₁ , qinv g₁ α₁ β₁) = e in 
              Ev f₁ (inl tt) → Ev g₁ (inl tt) → A ≃ B
    mk₁ {A} {B} (f , qinv g α β) (ev (inl tt) eq₁) (ev (inl tt) eq₂) = A≃B
      where
        equiv : (⊤ ⊔ A) ≃ (⊤ ⊔ B)
        equiv = (f , qinv g α β)

        elim-path : {X Y Z : Type₀} → (e : (⊤ ⊔ X) ≃ (⊤ ⊔ Y)) → (x : X) → 
           (fst e) (inl tt) == (fst e) (inr x) → Z
        elim-path e a path = ⊥-elim (bad-path tt a (injectivity e a path))

        mkf : (a : A) → Ev f (inr a) → B
        mkf a (ev (inl tt) eq) = elim-path equiv a (eq₁ ∙ ! eq)
        mkf a (ev (inr y) fx≡v) = y

        ff : A → B
        ff a = mkf a (mkV f (inr a))

        mkg : (b : B) → Ev g (inr b) → A
        mkg b (ev (inl tt) eq) = elim-path (sym≃ equiv) b (eq₂ ∙ ! eq)
        mkg b (ev (inr a) eq) = a

        gg : B → A
        gg b = mkg b (mkV g (inr b))

        mkα : (b : B) →  (e : Ev g (inr b)) → ff (mkg b e) == b
        mkα b (ev (inl tt) eq) = elim-path (sym≃ equiv) b (eq₂ ∙ ! eq)
        mkα b (ev (inr a) eq) = mkα' (mkV f (inr a))
          where
            mkα' : (ev : Ev f (inr a)) → mkf a ev == b
            mkα' (ev (inl tt) eq₃) = elim-path equiv a (eq₁ ∙ ! eq₃)
            mkα' (ev (inr _) eq₃) = inj₂≡ (! (ap f eq ∙ eq₃) ∙ α (inr b))

        αα : ∀ a -> (ff ∘ gg) a == a
        αα b = mkα b (mkV g (inr b))

        -- need to expand the definition of ff and gg "by hand" otherwise there is 
        -- nowhere to 'stick in' the explicit e₁ and e₂ we have.

        mkβ : (a : A) → (e₁ : Ev f (inr a)) → (e₂ : Ev g (inr (mkf a e₁))) →
              mkg (mkf a e₁) e₂ == a
        mkβ a (ev (inl tt) eq) _ = elim-path equiv a (eq₁ ∙ ! eq)
        mkβ a (ev (inr y) eq) (ev (inl tt) eq₃) =
          elim-path (sym≃ equiv) y (eq₂ ∙ ! eq₃)
        mkβ a (ev (inr _) eq) (ev (inr _) eq₃) =
          inj₂≡ (((! eq₃) ∙ ap g (! eq)) ∙ β (inr a))

        ββ : ∀ a -> (gg ∘ ff) a == a
        ββ a = let ev₁ = mkV f (inr a) in mkβ a ev₁ (mkV g (inr (mkf a ev₁)))

        A≃B : A ≃ B
        A≃B = ff , qinv gg αα ββ

    mk₁ (f , qinv g α β) (ev (inl tt) eq₁) (ev (inr a) eq₂) = 
      let e = (f , qinv g α β) in
      ⊥-elim
        (bad-path tt a
          (injectivity e a ((eq₁ ∙ ! (α (inl tt))) ∙ ap f eq₂)))
    mk₁ (f , qinv g α β) (ev (inr b) eq₁) (ev (inl tt) eq₂) = 
     ⊥-elim  (bad-path tt b (((! (α (inl tt))) ∙ ap f eq₂) ∙ eq₁))
    mk₁ {A} {B} (f , qinv g α β) (ev (inr x) ftt=x) (ev (inr y) gtt=y) =
      A≃B
      where
        equiv : (⊤ ⊔ A) ≃ (⊤ ⊔ B)
        equiv = (f , qinv g α β)

        elim-path : {X Y Z : Type₀} → (e : (⊤ ⊔ X) ≃ (⊤ ⊔ Y)) → (x : X) → 
           (fst e) (inl tt) == (fst e) (inr x) → Z
        elim-path e a path = ⊥-elim (bad-path tt a (injectivity e a path))

        mkf : (a : A) → Ev f (inr a) → B
        mkf a (ev (inl tt) _) = x
        mkf a (ev (inr y) _) = y

        ff : A → B
        ff a = mkf a (mkV f (inr a))

        mkg : (b : B) → Ev g (inr b) → A
        mkg b (ev (inl tt) eq) = y
        mkg b (ev (inr a) eq) = a

        gg : B → A
        gg b = mkg b (mkV g (inr b))

        mkα : (b : B) →  (e₁ : Ev g (inr b)) → (e₂ : Ev f (inr (mkg b e₁))) →
              mkf (mkg b e₁) e₂ == b
        mkα b (ev (inl tt) gb=tt) (ev (inl tt) fgb=tt) =
          inj₂≡ (! ftt=x ∙ ! (ap f gb=tt) ∙ α (inr b))
        mkα b (ev (inl tt) gb=tt) (ev (inr y₁) fy=y₁) =
          elim-path
            (sym≃ equiv)
            y₁
            ( ! ((! (ap g fy=y₁) ∙ β (inr y)) ∙ (! gtt=y)))
        mkα b (ev (inr z) gb=z) (ev (inl tt) fgb=tt) =
          elim-path
            (sym≃ equiv) b ((ap g (! fgb=tt) ∙ β (inr z)) ∙ (! gb=z))
        mkα b (ev (inr z) gb=z) (ev (inr z₂) fgb=z₂) = 
            let path = (ap g (! fgb=z₂) ∙ β (inr z)) ∙ ! gb=z in
            inj₂≡ (inj≃ (sym≃ equiv) (inr z₂) (inr b)  path)

        αα : ∀ a -> (ff ∘ gg) a == a
        αα b = let ev₁ = mkV g (inr b) in mkα b ev₁ (mkV f (inr (mkg b ev₁)))

        -- need to expand the definition of ff and gg "by hand"
        -- otherwise there is nowhere to 'stick in' the explicit e₁
        -- and e₂ we have.

        mkβ : (a : A) → (e₁ : Ev f (inr a)) →
          (e₂ : Ev g (inr (mkf a e₁))) → mkg (mkf a e₁) e₂ == a
        mkβ a (ev (inl tt) eq) (ev (inl _) eq₃) =
          inj₂≡ (! (ap g eq ∙ gtt=y) ∙ β (inr a))
        mkβ a (ev (inl tt) eq) (ev (inr y₁) eq₃) =
          elim-path equiv y₁ ((ftt=x ∙ (! (α (inr x)))) ∙ ap f eq₃)
        mkβ a (ev (inr z) fa=z) (ev (inl tt) eq₃) =
          elim-path equiv a ((ap f (! eq₃) ∙ α (inr z)) ∙ (! fa=z) )
        mkβ a (ev (inr _) fa=y) (ev (inr _) eq₃) =
          inj₂≡ (((! eq₃) ∙ ap g (! fa=y)) ∙ β (inr a))

        ββ : ∀ a -> (gg ∘ ff) a == a
        ββ a = let ev₁ = mkV f (inr a) in mkβ a ev₁ (mkV g (inr (mkf a ev₁)))

        A≃B : A ≃ B
        A≃B = ff , qinv gg αα ββ


left-cancel-≃ : {A B : Type₀} →  ((⊤ ⊔ A) ≃ (⊤ ⊔ B)) ≃ (A ≃ B)
left-cancel-≃ 