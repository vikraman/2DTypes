{-# OPTIONS --without-K #-}

module Pi2.UniFibExamples where

open import UnivalentTypeTheory
open import Surjections
open import PropositionalTruncation
open import SetTruncation

----------------------------------------------------------------------
-- To migrate to lib
----------------------------------------------------------------------

module _ {ℓ} where

  Ω : (X : Type ℓ) → X → Type ℓ
  Ω X x = x == x

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  ⊩∥-prsrv-eqv : X ≃ Y → ∥ X ∥ ≃ ∥ Y ∥
  ⊩∥-prsrv-eqv (f , g , c) = logical-eqv identify identify
                                         (recTrunc _ (∣_∣ ∘ f) identify)
                                         (recTrunc _ (∣_∣ ∘ g) identify)

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {P : X → Type ℓ₂} where

  ∥dpair=∥ : ((x : X) → is-prop (P x))
            → {x x' : X} → (y : P x) → (y' : P x')
            → ∥ x == x' ∥ → ∥ (x , y) == (x' , y') ∥
  ∥dpair=∥ φ {x} {x'} y y' = indTrunc _ f (λ p → identify)
    where f : x == x' → ∥ (x , y) == (x' , y') ∥
          f p = ∣ dpair= (p , φ x' (tpt P p y) y') ∣


module _ {ℓ} where

  ∥prop∥-out : {X : Type ℓ} → is-prop X → ∥ X ∥ → X
  ∥prop∥-out φ = recTrunc _ id φ

  ∥prop∥ : {X : Type ℓ} → is-prop X → ∥ X ∥ ≃ X
  ∥prop∥ φ = logical-eqv identify φ (∥prop∥-out φ) ∣_∣

  ∥-∥-idem-out : {X : Type ℓ} → ∥ ∥ X ∥ ∥ → ∥ X ∥
  ∥-∥-idem-out = ∥prop∥-out identify

  ∥-∥-idem : (X : Type ℓ) → ∥ ∥ X ∥ ∥ ≃ ∥ X ∥
  ∥-∥-idem X = ∥prop∥ identify

module _ {ℓ} {X : Type ℓ} where

  infixr 80 _∥◾∥_
  _∥◾∥_ : {x y z : X} → ∥ x == y ∥ → ∥ y == z ∥ → ∥ x == z ∥
  _∥◾∥_ {x} {y} {z} = indTrunc _ f (λ _ → Π-prsrv-prop (λ _ → identify))
    where f : {x y z : X} → x == y → ∥ y == z ∥ → ∥ x == z ∥
          f {z = z} (refl y) = indTrunc _ ∣_∣ (λ _ → identify)

  infix 100 ∥!∥
  ∥!∥ : {x y : X} → ∥ x == y ∥ → ∥ y == x ∥
  ∥!∥ = indTrunc _ (∣_∣ ∘ !) (λ _ → identify)

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {P : X → Type ℓ₂} where

  dpair=-prop : {φ : (x : X) → is-prop (P x)}
                → {x x' : X} → {y : P x} → {y' : P x'}
                → x == x' → (x , y) == (x' , y')
  dpair=-prop {φ = φ} (refl x) = dpair= (refl x , φ x _ _)

-- module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} where

  -- paths-in-Σ-prop : (P : X → Type ℓ₂) → ((x : X) → is-prop (P x))
  --                   → {x x' : X} → (y : P x) → (y' : P x')
  --                   → (x == x') ≃ ((x , y) == (x' , y'))
  -- paths-in-Σ-prop P φ y y' = dpair=-prop {P = P} {φ} {y = y} {y'} ,
  --                            {!!}


module _ {ℓ} where

  is-path-conn : (X : Type ℓ) → Type ℓ
  is-path-conn X = ∥ X ∥ × ((x y : X) → ∥ x == y ∥)

  is-0-conn : (X : Type ℓ) → Type ℓ
  is-0-conn X = is-contr ∥ X ∥₀

  -- 0-conn-prop : (X : Type ℓ) → is-0-conn X ≃ is-path-conn X
  -- 0-conn-prop = {!!}


----------------------------------------------------------------------


module _ {ℓ : Level} where

  BAut : (X : Type ℓ) → Type (lsuc ℓ)
  BAut X = Σ (Type ℓ) (λ Y → ∥ Y ≃ X ∥)

  pr₁ : {X : Type ℓ} → BAut X → Type ℓ
  pr₁ (Y , q) = Y

  b₀ : {X : Type ℓ} → BAut X
  b₀ {X} = X , ∣ ide X ∣

  tpt-eqv-pr₁ : {X : Type ℓ} → {v w : BAut X} → (p : v == w)
                → p₁ (tpt-eqv pr₁ p) == tpt id (dpair=-e₁ p)
  tpt-eqv-pr₁ (refl v) = refl id

  is-univ-fib-pr₁ : {X : Type ℓ} → is-univ-fib (pr₁ {X})
  is-univ-fib-pr₁ (Y , q) (Y' , r) = qinv-is-equiv (g , η , ε)
    where g : Y ≃ Y' → Y , q == Y' , r
          g e = dpair= (ua e , identify _ _)
          η : g ∘ tpt-eqv pr₁ ∼ id
          η (refl w) = ap dpair= (dpair= (ua-ide Y , prop-is-set identify _ _ _ _))
          ε : tpt-eqv pr₁ ∘ g ∼ id
          ε e = eqv= (tpt-eqv-pr₁ (dpair= (ua e , identify _ _))
                      ◾ ap (tpt id) (dpair=-β₁ (ua e , identify _ _)) ◾ ua-β₁ e)
          -- τ : ap (tpt-eqv pr₁) ∘ η ∼ ε ∘ tpt-eqv pr₁
          -- τ (refl w) = {!!}

  ΩBAut≃Aut : (X : Type ℓ) → (Ω (BAut X) b₀) ≃ (X ≃ X)
  ΩBAut≃Aut X = tpt-eqv pr₁ , is-univ-fib-pr₁ b₀ b₀

module _ {ℓ} where

  Σ-Type-is : (X : Type ℓ) → Type (lsuc ℓ)
  Σ-Type-is X = Σ (Type ℓ) (λ Y → ∥ Y == X ∥)

  BAut≃Σ-Type-is : (X : Type ℓ) → BAut X ≃ Σ-Type-is X
  BAut≃Σ-Type-is X = Σ-fib-eqv (λ Y → ⊩∥-prsrv-eqv (!e (path-to-eqv , univalence _ _)))


module _ {ℓ} where

  Σ-Type-is-is-path-conn : (X : Type ℓ) → is-path-conn (Σ-Type-is X)
  Σ-Type-is-is-path-conn X = ∣ (X , ∣ refl X ∣) ∣ , ψ
    where ψ : (x y : Σ-Type-is X) → ∥ x == y ∥
          ψ (X , p) (Y , q) = ∥dpair=∥ (λ _ → identify) p q (p ∥◾∥ ∥!∥ q)

module _ {ℓ} where
  -- TODO: Make a special case of paths-in-Σ-prop

  paths-in-Σ-Type-is : {X Y Z : Type ℓ} → (p : ∥ Y == X ∥) → (q : ∥ Z == X ∥)
                       → (Y == Z) ≃ ((Y , p) == (Z , q))
  paths-in-Σ-Type-is p q =
    (λ α → dpair= (α , identify _ _)) ,
    (qinv-is-equiv (dpair=-e₁ ,
                   (λ α → dpair=-β₁ _) ,
                   (λ α' → ap dpair= (dpair= ((refl _) ,
                                               (prop-is-set identify _ _ _ _)))
                            ◾ dpair=-η _)))

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} where

  lem1 : (P : X → Type ℓ₂)
         → is-path-conn X → (x y : X) → ∥ (P x ≃ P y) ∥
  lem1 P (x , φ) = f φ
       where f : ((x y : X) → ∥ x == y ∥) → (x y : X) → ∥ (P x ≃ P y) ∥
             f φ x y = indTrunc (λ p → ∥ (P x ≃ P y) ∥) (∣_∣ ∘ path-to-eqv ∘ ap P)
                                (λ _ → identify) (φ x y)

  lem2 : {Y : Type ℓ₂} → (e : ∥ X ≃ Y ∥) → is-set X → is-set Y
  lem2 {Y = Y} = indTrunc _ (λ e → retract-prsrv-set (equiv-is-retract e))
                          (λ e → Π-prsrv-prop (λ φ → is-set-is-prop _))

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} where
  -- TODO: generalize this to the fact that fibers over a
  -- path-connected space have the same truncation level

  lem3 : (P : X → Type ℓ₂) → is-path-conn X
         → (x y : X) → is-set (P x) → is-set (P y)
  lem3 P φ x y = lem2 (lem1 P φ x y)

module _ {ℓ₁} {X : Type ℓ₁} where
  -- Provable without univalence?

  lem5 : is-set X → is-set (X == X)
  lem5 φ = retract-prsrv-set (equiv-is-retract (!e (path-to-eqv , univalence _ _)))
                             (eqv-prsrv-set φ)

  lem4 : is-set X → is-set (Ω (Σ-Type-is X) (X , ∣ refl X ∣))
  lem4 φ = retract-prsrv-set (equiv-is-retract (paths-in-Σ-Type-is _ _)) (lem5 φ)


module _ {ℓ} {X : Type ℓ} where
  -- TODO : If X is n-truncated then (Σ-Type-is X) is (n+1)-truncated
  -- Here is a special case.

  Σ-Type-is-incr-lvl : is-set X → is-1type (Σ-Type-is X)
  Σ-Type-is-incr-lvl φ (Y , p) (Z , q) = lem3 (paths-l (Y , p) id)
                               (Σ-Type-is-is-path-conn X)
                               (Y , p) (Z , q)
                               (lem3 loops
                                     (Σ-Type-is-is-path-conn X)
                                     (X , ∣ refl X ∣) (Y , p) (lem4 φ))
