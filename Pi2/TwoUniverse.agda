{-# OPTIONS --without-K #-}

module Pi2.TwoUniverse where

open import UnivalentTypeTheory
open import PropositionalTruncation
open import SetTruncation
open import OneTypes
open import Surjections

open import Pi2.UniFibExamples

----------------------------------------------------------------------
-- To be migrated to lib
----------------------------------------------------------------------

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {P : X → Type ℓ₂} where

  tpt◾↓ : {x y z : X} {u : P x} {v : P y} {w : P z}
        → (p : x == y) (r : tpt P p u == v)
        → (q : y == z) (s : tpt P q v == w)
        → tpt P (p ◾ q) u == w
  tpt◾↓ (refl x) (refl p) (refl .x) (refl .p) = refl p

  dpair=◾ : {x y z : X} {u : P x} {v : P y} {w : P z}
          → (p : x == y) (r : tpt P p u == v)
          → (q : y == z) (s : tpt P q v == w)
          → dpair= (p , r) ◾ dpair= (q , s) == dpair= (p ◾ q , tpt◾↓ p r q s)
  dpair=◾ (refl x) (refl p) (refl .x) (refl .p) = refl (refl (x , p))

module _ {ℓ} {X Y : Type ℓ} where

  ap-path-to-eqv-out : {p q : X == Y}
                       → (path-to-eqv p == path-to-eqv q) → (p == q)
  ap-path-to-eqv-out {p} {q} α = ! (ua-η p) ◾ ap ua α ◾ ua-η q

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {P : X → Type ℓ₂} where

  ap-dpair=-e-out : {x y : X} → {ux : P x} → {uy : P y}
                     → {p q : (x , ux) == (y , uy)}
                     → (α : dpair=-e₁ p == dpair=-e₁ q)
                     → (tpt _ α (dpair=-e₂ p) == dpair=-e₂ q)
                     → (p == q)
  ap-dpair=-e-out {p = p} {q} α β = ! (dpair=-η p)
                                    ◾ ap dpair= (dpair= (α , β))
                                    ◾ dpair=-η q


module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X : Type ℓ₁} {Y : Type ℓ₂}
         {X' : Type ℓ₃} {Y' : Type ℓ₄} where

  +fn : (X → Y) → (X' → Y') → X + X' → Y + Y'
  +fn f f' (i₁ x) = i₁ (f x)
  +fn f f' (i₂ x') = i₂ (f' x')

----------------------------------------------------------------------


is-type : ∀ {ℓ} (T : Type ℓ) → _
is-type T = λ X → ∥ X == T ∥

is-𝟚 = is-type 𝟚

U[𝟚] : Type₁
U[𝟚] = Σ Type₀ is-𝟚

El[𝟚] : U[𝟚] → Type₀
El[𝟚] = p₁

Ũ = Σ U[𝟚] El[𝟚]

-- Labels for some of the pertinent terms
`𝟚 : U[𝟚]
`𝟚 = (𝟚 , ∣ refl 𝟚 ∣)

`id : {A : U[𝟚]} → A == A
`id {A} = refl A

`not : `𝟚 == `𝟚
`not = dpair= (ua not-eqv , identify _ _)

not∘not=id : not ∘ not == id
not∘not=id = funext λ { 0₂ → refl 0₂ ; 1₂ → refl 1₂ }

note●note=ide : not-eqv ● not-eqv == ide 𝟚
note●note=ide = eqv= not∘not=id

notp◾notp=refl : ua not-eqv ◾ ua not-eqv == refl 𝟚
notp◾notp=refl = ! (ua-● not-eqv not-eqv)
               ◾ ap ua note●note=ide
               ◾ ua-ide 𝟚

`ρ : `not ◾ `not == `id
`ρ = dpair=◾ (ua not-eqv) (identify _ _) (ua not-eqv) (identify _ _)
     ◾ ap dpair= (dpair= (notp◾notp=refl , prop-is-set identify _ _ _ _))

module ComputationalProperties where

  path-to-eqv[𝟚] : (p : `𝟚 == `𝟚) → 𝟚 → 𝟚
  path-to-eqv[𝟚] p = p₁ (path-to-eqv (dpair=-e₁ p))

  `id-β : (x : El[𝟚] `𝟚) → path-to-eqv[𝟚] `id x == x
  `id-β = refl

  `not-β : (x : El[𝟚] `𝟚) → path-to-eqv[𝟚] `not x == not x
  `not-β x = ap (λ p → (p₁ ∘ path-to-eqv) p x) {y = ua not-eqv} (dpair=-β₁ _)
           ◾ ap (λ p → (p₁ p) x) (ua-β not-eqv)

module ZeroDimensionalTerms where

  U[𝟚]-is-path-conn : is-path-conn U[𝟚]
  U[𝟚]-is-path-conn = Σ-Type-is-is-path-conn 𝟚

open ZeroDimensionalTerms public

module OneDimensionalTerms where

  module EquivBool where

    data Singleton {a} {A : Set a} (x : A) : Set a where
      _with=_ : (y : A) → x == y → Singleton x

    inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
    inspect x = x with= (refl x)

    φ-𝟘 : (f : 𝟚 → 𝟚) → (e : is-equiv f)
          → Σ 𝟚 (λ b → (f 0₂ == b) × (f 1₂ == b)) → 𝟘
    φ-𝟘 f (g , η , ε , τ) (b , (p , q)) = 0₂≠1₂ (! (η 0₂) ◾ ap g (p ◾ ! q) ◾ η 1₂)

    φ : (f : 𝟚 → 𝟚) → (e : is-equiv f) → (f == id) + (f == not)
    φ f e with inspect (f 0₂) | inspect (f 1₂)
    φ f e        | 0₂ with= p | 0₂ with= q = rec𝟘 _ (φ-𝟘 f e (0₂ , (p , q)))
    φ f e        | 0₂ with= p | 1₂ with= q = i₁ (funext (ind𝟚 _ p q))
    φ f e        | 1₂ with= p | 0₂ with= q = i₂ (funext (ind𝟚 _ p q))
    φ f e        | 1₂ with= p | 1₂ with= q = rec𝟘 _ (φ-𝟘 f e (1₂ , (p , q)))

    ψ : {f : 𝟚 → 𝟚} → {e : is-equiv f}
        → (f == id) + (f == not) → ((f , e) == ide 𝟚) + ((f , e) == not-eqv)
    ψ (i₁ p) = i₁ (eqv= p)
    ψ (i₂ p) = i₂ (eqv= p)

    all-eqvs-𝟚 : (e : 𝟚 ≃ 𝟚) → (e == ide 𝟚) + (e == not-eqv)
    all-eqvs-𝟚 (f , e') = ψ (φ f e')

  open EquivBool using (all-eqvs-𝟚)

  all-1-paths-𝟚 : (l : 𝟚 == 𝟚) → (l == refl 𝟚) + (l == ua not-eqv)
  all-1-paths-𝟚 = φ ∘ all-eqvs-𝟚 ∘ path-to-eqv
    where φ : {l : 𝟚 == 𝟚} → (path-to-eqv l == ide 𝟚) + (path-to-eqv l == not-eqv)
              → (l == refl 𝟚) + (l == ua not-eqv)
          φ (i₁ α) = i₁ (ap-path-to-eqv-out {q = refl 𝟚} (α ◾ ! (ua-β (ide 𝟚)) ◾ ap path-to-eqv (ua-ide 𝟚)))
          φ (i₂ α) = i₂ (ap-path-to-eqv-out (α ◾ ! (ua-β not-eqv)))

  all-1-paths : (p : `𝟚 == `𝟚) → (p == `id) + (p == `not)
  all-1-paths = φ ∘ all-1-paths-𝟚 ∘ dpair=-e₁
    where φ : {l : `𝟚 == `𝟚} → (dpair=-e₁ l == refl 𝟚) + (dpair=-e₁ l == ua not-eqv)
              → (l == `id) + (l == `not)
          φ {l} (i₁ α) = i₁ (ap-dpair=-e-out (α ◾ ! (dpair=-β₁ {P = is-𝟚} {ux = ∣ refl 𝟚 ∣} _))
                                             (prop-is-set identify _ _ _ _))
          φ {l} (i₂ α) = i₂ (ap-dpair=-e-out (α ◾ ! (dpair=-β₁ _))
                                             (prop-is-set identify _ _ _ _))

  open ComputationalProperties

  ¬id=not : ¬ (`id == `not)
  ¬id=not id=not = rec𝟘 _ (0!=1 ((! (`id-β 0₂) ◾ ap (λ p → path-to-eqv[𝟚] p 0₂) id=not ◾ `not-β 0₂)))
    where
    0!=1 : ¬ (0₂ == 1₂)
    0!=1 ()

  !not=not : ! `not == `not
  !not=not with all-1-paths (! `not)
  !not=not | i₁ !not=id = rec𝟘 _ (¬id=not id=not)
    where
    id=not : `id == `not
    id=not = ! (◾invl `not) ◾ ap (λ x → x ◾ `not) !not=id ◾ ◾unitl `not
  !not=not | i₂ !not=not = !not=not

open OneDimensionalTerms public using (all-1-paths)

module TwoDimensionalTerms where

  𝟚-is-set : is-set 𝟚
  𝟚-is-set = retract-prsrv-set (equiv-is-retract 𝟙+𝟙≃𝟚)
                               (+-prsrv-set (contr-is-set 𝟙-is-contr)
                                            (contr-is-set 𝟙-is-contr))

  U[𝟚]-is-1type : is-1type U[𝟚]
  U[𝟚]-is-1type = Σ-Type-is-incr-lvl 𝟚-is-set

  all-2-paths-id : (u : `id {`𝟚} == `id) → u == refl `id
  all-2-paths-id u = U[𝟚]-is-1type _ _ _ _ u (refl `id)

  all-2-paths-not : (u : `not == `not) → u == refl `not
  all-2-paths-not u = U[𝟚]-is-1type _ _ _ _ u (refl `not)

open TwoDimensionalTerms public using (U[𝟚]-is-1type)
