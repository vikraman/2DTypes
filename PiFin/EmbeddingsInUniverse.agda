{-# OPTIONS --without-K #-}

module PiFin.EmbeddingsInUniverse where

open import UnivalentTypeTheory
open import PropositionalTruncation

---------------------------------------------------------------------------
-- Library code
---------------------------------------------------------------------------

module _ {ℓ} {X : Type ℓ} where

  infixr 80 _∥◾∥_
  _∥◾∥_ : {x y z : X} → ∥ x == y ∥ → ∥ y == z ∥ → ∥ x == z ∥
  _∥◾∥_ {x} {y} {z} = indTrunc _ f (λ _ → Π-prsrv-prop (λ _ → identify))
    where f : {x y z : X} → x == y → ∥ y == z ∥ → ∥ x == z ∥
          f {z = z} (refl y) = indTrunc _ ∣_∣ (λ _ → identify)

  infix 100 ∥!∥
  ∥!∥ : {x y : X} → ∥ x == y ∥ → ∥ y == x ∥
  ∥!∥ = indTrunc _ (∣_∣ ∘ !) (λ _ → identify)

module _ {ℓ₁ ℓ₂} {P : Type ℓ₁ → Type ℓ₂} where

  tpt-eqv-p₁ : {X Y : Type ℓ₁} → (p : X == Y)
               → {ux : P X} → {uy : P Y} → (up : tpt P p ux == uy)
               → tpt-eqv p₁ (dpair= (p , up)) == path-to-eqv p
  tpt-eqv-p₁ (refl x) (refl ux) = refl (ide x)

---------------------------------------------------------------------------


module _ {ℓ₁ ℓ₂} where

{-
  The subobject classifier true : 𝟙 → Ω in HoTT is an
  embedding. Mere predicates on the universe are formalized as
  either maps into Ω or, equivalently, as type families of
  propositions indexed by the universe. HoTT has homotopy pullbacks
  and of course, these pullbacks preserve embeddings. Thus, any
  type family of propositions over U determines a
  subobject of/embedding into the universe. The domain of such an
  embedding is the base of a univalent fibration: namely, that
  obtained by pulling back the universe fibration Ũ → U over the
  embedding.

  We condense this argument into a single useful theorem.
-}

  pred-ext-is-univ : (Q : Type ℓ₁ → Type ℓ₂) → (φ : (X : Type ℓ₁) → is-prop (Q X))
                     → is-univ-fib (p₁ {X = Type ℓ₁} {Q})
  pred-ext-is-univ Q φ (X , q) (X' , q') = qinv-is-equiv (g , η , ε)
     where f = tpt-eqv p₁
           g : X ≃ X' → X , q == X' , q'
           g e = dpair= (ua e , φ X' _ _)
           η : g ∘ f ∼ id
           η (refl (X , _)) = ! (dpair=-η _)
                              ◾ ap dpair= (dpair= (dpair=-β₁ _ ◾ ua-ide X ,
                                                   prop-is-set (φ X) _ _ _ _))
                              ◾ dpair=-η _
           ε : f ∘ g ∼ id
           ε e = tpt-eqv-p₁ (ua e) _ ◾ ua-β e

{- Examples -}

module _ {ℓ} where

  singleton-pred : (X Y : Type ℓ) → Type (lsuc ℓ)
  singleton-pred X Y = ∥ Y == X ∥

  singleton-subuniv : (F : Type ℓ) → is-univ-fib (p₁ {X = Type ℓ} {singleton-pred F})
  singleton-subuniv F = pred-ext-is-univ (singleton-pred F) (λ X → identify)



module UnivalentUniverseOfZeroAndOne where

  data Names : Type₀ where
    `0 : Names
    `1 : Names

  El : Names → Type₀
  El `0 = 𝟘
  El `1 = 𝟙

  is-𝟘-or-𝟙 : Type₀ → Type₁
  is-𝟘-or-𝟙 X = Σ Names (λ Y → ∥ X == El Y ∥)

  𝟘-or-𝟙-is-prop : (X : Type₀) → is-prop(is-𝟘-or-𝟙 X)
  𝟘-or-𝟙-is-prop X (`0 , p) (`0 , q) = dpair= (refl `0 , identify _ _)
  𝟘-or-𝟙-is-prop X (`0 , p) (`1 , q) =
    rec𝟘 _ (recTrunc 𝟘 (λ p → tpt id p 0₁) 𝟘-is-prop (∥!∥ q ∥◾∥ p))
  𝟘-or-𝟙-is-prop X (`1 , p) (`0 , q) =
    rec𝟘 _ (recTrunc 𝟘 (λ p → tpt id p 0₁) 𝟘-is-prop (∥!∥ p ∥◾∥ q))
  𝟘-or-𝟙-is-prop X (`1 , p) (`1 , q) = dpair= (refl `1 , identify _ _)

  𝟘-or-𝟙-is-univ : is-univ-fib (p₁ {X = Type₀} {is-𝟘-or-𝟙})
  𝟘-or-𝟙-is-univ = pred-ext-is-univ is-𝟘-or-𝟙 𝟘-or-𝟙-is-prop


---------------------------------------------------------------------------
-- Library code for UnivalentUniverseOfFiniteTypes
---------------------------------------------------------------------------

module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type ℓ₁} {Y : Type ℓ₂} {Z : Type ℓ₃} {x : X} {y : Y} where

  i₂-𝟘-e : i₂ x == i₁ y → Z
  i₂-𝟘-e p = rec𝟘 Z (¬𝟘' (i₂=-e p))


module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂}
         (f : 𝟙 + X → 𝟙 + Y) (g : 𝟙 + Y → 𝟙 + X) (η : g ∘ f ∼ id) where

  rest-aux : (x : X)
             → Σ (𝟙 + Y) (λ v → f (i₁ 0₁) == v)
             → Σ (𝟙 + Y) (λ w → f (i₂ x) == w)
             → Y
  rest-aux x ((i₁ 0₁) , p) ((i₁ 0₁) , q) =
           i₂-𝟘-e (! (η _) ◾ ap g q ◾ ap g (! p) ◾ η _)
  rest-aux x ((i₁ 0₁) , p) ((i₂ y') , q) = y'
  rest-aux x ((i₂ y) , p) ((i₁ 0₁) , q) = y
  rest-aux x ((i₂ y) , p) ((i₂ y') , q) = y'

  rest : X → Y
  rest x = rest-aux x (f (i₁ 0₁) , refl (f (i₁ 0₁))) (f (i₂ x) , refl (f (i₂ x)))

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂}
         (f : 𝟙 + X → 𝟙 + Y) (g : 𝟙 + Y → 𝟙 + X) (η : g ∘ f ∼ id) where

  rest-aux-β : (x : X)
               → (w : 𝟙 + Y) → (p : f (i₁ 0₁) == w)
               → (v : 𝟙 + Y) → (q : f (i₂ x) == v)
               → rest f g η x == rest-aux f g η x (w , p) (v , q)
  rest-aux-β x w p v q =
             ap (λ γ → rest-aux f g η x γ (f (i₂ x) , refl _))
                (dpair= (p , refl _))
             ◾ ap (λ γ → rest-aux f g η x (w , γ) (f (i₂ x) , refl _))
                  (tpt=l _ p (refl _) ◾ ◾unitl _)
             ◾ ap (λ γ → rest-aux f g η x (w , p) γ)
                  (dpair= (q , (refl _)))
             ◾ ap (λ γ → rest-aux f g η x (w , p) (v , γ))
                  (tpt=l _ q (refl _) ◾ ◾unitl _)

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂}
         (f : 𝟙 + X → 𝟙 + Y) (g : 𝟙 + Y → 𝟙 + X)
         (η : g ∘ f ∼ id) (ε : f ∘ g ∼ id) where

  rest-η-aux : (x : X)
               → (u : Σ (𝟙 + Y) (λ w → f (i₁ 0₁) == w))
               → (v : Σ (𝟙 + Y) (λ w → f (i₂ x) == w))
               → Σ (𝟙 + X) (λ w → g (i₁ 0₁) == w)
               → Σ (𝟙 + X) (λ w → g (p₁ u) == w)
               → Σ (𝟙 + X) (λ w → g (p₁ v) == w)
               → rest g f ε (rest f g η x) == x
  -- not monic
  rest-η-aux x (i₁ 0₁ , p) (i₁ 0₁ , q) _ _ _ =
             i₂-𝟘-e (! (η _) ◾ ap g q ◾ ! (ap g p) ◾ η _)
  rest-η-aux x (u , p) (v , q) _ (i₁ 0₁ , r) (i₁ 0₁ , s) =
             i₂-𝟘-e (! (η (i₂ x)) ◾ ap g q
                    ◾ ap g (! (ε v) ◾ ap f s ◾ ! (ap f r) ◾ ε u)
                    ◾ ! (ap g p) ◾ η (i₁ 0₁))
  rest-η-aux x (i₂ y , p) (i₂ y' , q) (i₁ 0₁ , t) (i₁ 0₁ , r) (i₂ x'' , s) =
             i₂-𝟘-e (! (ε _) ◾ ap f (r ◾ ! t) ◾ ε _)

  -- g ∘ f does not preserve 0₁
  rest-η-aux x (_ , p) _ _ (i₂ x' , r) _ =
             i₂-𝟘-e (! r ◾ ! (ap g p) ◾ η (i₁ 0₁))

  rest-η-aux x (i₂ y , p) (i₂ y' , q) (i₂ x' , t) (i₁ 0₁ , r) (i₂ x'' , s) =
             ap (rest g f ε) (rest-aux-β f g η x (i₂ y) p (i₂ y') q)
             ◾ rest-aux-β g f ε y' (i₂ x') t (i₂ x'') s
             ◾ i₂=-e (! s ◾ ! (ap g q) ◾ η (i₂ x))
  rest-η-aux x (i₁ 0₁ , p) (i₂ y' , q) _ (i₁ 0₁ , r) (i₂ x'' , s) =
             ap (rest g f ε) (rest-aux-β f g η x (i₁ 0₁) p (i₂ y') q)
             ◾ rest-aux-β g f ε y' (i₁ 0₁) r (i₂ x'') s
             ◾ i₂=-e (! s ◾ ! (ap g q) ◾ η (i₂ x))
  rest-η-aux x (i₂ y , p) (i₁ 0₁ , q) _ (i₁ 0₁ , r) (i₂ x'' , s) =
             ap (rest g f ε) (rest-aux-β f g η x (i₂ y) p (i₁ 0₁) q)
             ◾ rest-aux-β g f ε y (i₂ x'') s (i₁ 0₁) r
             ◾ i₂=-e (! s ◾ ! (ap g q) ◾ η (i₂ x))

  rest-η : (x : X) → rest g f ε (rest f g η x) == x
  rest-η x = rest-η-aux x (f (i₁ 0₁) , refl _) (f (i₂ x) , refl _)
                        (g (i₁ 0₁) , refl _) (g (f (i₁ 0₁)) , refl _)
                        (g (f (i₂ x)) , refl _)

module _ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} where

  +cncl𝟙l' : 𝟙 + X ≃ 𝟙 + Y → X ≃ Y
  +cncl𝟙l' (f , g , η , ε , τ) = rest f g η ,
                                 (qinv-is-equiv (rest g f ε ,
                                                 rest-η f g η ε ,
                                                 rest-η g f ε η))

module _ {ℓ} {X Y : Type ℓ} where

  +cncl𝟙l : 𝟙 + X == 𝟙 + Y → X == Y
  +cncl𝟙l = ua ∘ +cncl𝟙l' ∘ path-to-eqv


module UnivalentUniverseOfFiniteTypes where
  El : ℕ → Type₀
  El 0 = 𝟘
  El (succ X) = 𝟙 + (El X)

  module PathsInℕ where

    code : ℕ → ℕ → Type₀
    code 0 0 = 𝟙
    code 0 (succ Y) = 𝟘
    code (succ X) 0 = 𝟘
    code (succ X) (succ Y) = code X Y

    code-rfl : (X : ℕ) → code X X
    code-rfl 0 = 0₁
    code-rfl (succ X) = code-rfl X

    enc : {X Y : ℕ} → X == Y → code X Y
    enc (refl X) = code-rfl X

    enc-absorbs-1+ : {X Y : ℕ} → enc ∘ (ap succ) ∼ enc {X} {Y}
    enc-absorbs-1+ (refl X) = refl (code-rfl X)

    dec : {X Y : ℕ} → code X Y → X == Y
    dec {0} {0} 0₁ = refl 0
    dec {0} {succ Y} ()
    dec {succ X} {0} ()
    dec {succ X} {succ Y} = ap succ ∘ dec {X} {Y}

    dec-code-rfl : (X : ℕ) → dec (code-rfl X) == refl X
    dec-code-rfl 0 = refl (refl 0)
    dec-code-rfl (succ X) = ap (ap succ) (dec-code-rfl X)


    enc-η : {X Y : ℕ} → dec ∘ enc {X} {Y} ∼ id
    enc-η (refl X) = dec-code-rfl X

    enc-ε : {X Y : ℕ} → enc ∘ dec {X} {Y} ∼ id
    enc-ε {0} {0} 0₁ = refl 0₁
    enc-ε {0} {succ Y} ()
    enc-ε {succ X} {0} ()
    enc-ε {succ X} {succ Y} c = enc-absorbs-1+ (dec {X} {Y} c) ◾ enc-ε {X} {Y} c

    enc-τ : {X Y : ℕ} → ap enc ∘ enc-η ∼ enc-ε {X} {Y} ∘ enc {X} {Y}
    enc-τ (refl 0) = refl (refl 0₁)
    enc-τ (refl (succ X)) = ! (ap∘ enc (ap succ) (dec-code-rfl X))
                           ◾ l₂=!l₁◾r (nat (!h enc-absorbs-1+) (dec-code-rfl X))
                           ◾ (!! (enc-absorbs-1+ (dec (code-rfl X)))
                              [2,0,1] ap enc (dec-code-rfl X) ◾ !h (enc-absorbs-1+) (refl X))
                           ◾ (enc-absorbs-1+ (dec (code-rfl X))
                              [1,0,2] (◾unitr (ap enc (dec-code-rfl X))))
                           ◾ (enc-absorbs-1+ (dec (code-rfl X)) [1,0,2] enc-τ (refl X))

    enc-eqv : (X Y : ℕ) → (X == Y) ≃ code X Y
    enc-eqv X Y = enc , dec , enc-η , enc-ε {X} {Y} , enc-τ

    ---

    code-is-prop : (X Y : ℕ) → is-prop(code X Y)
    code-is-prop 0 0 = contr-is-prop (𝟙-is-contr)
    code-is-prop 0 (succ Y) = 𝟘-is-prop
    code-is-prop (succ X) 0 = 𝟘-is-prop
    code-is-prop (succ X) (succ Y) = code-is-prop X Y

    ℕ-is-set' : is-set ℕ
    ℕ-is-set' X Y = retract-prsrv-prop (equiv-is-retract (!e (enc-eqv X Y)))
                                        (code-is-prop X Y)

    ----

    reflect : (X Y : ℕ) → El X == El Y → X == Y
    reflect 0 0 p = refl 0
    reflect 0 (succ Y) p = rec𝟘 _ (tpt id (! p) (i₁ 0₁))
    reflect (succ X) 0 p = rec𝟘 _ (tpt id p (i₁ 0₁))
    reflect (succ X) (succ Y) p = ap succ (reflect X Y (+cncl𝟙l {X = El X} p))

    ---

    El-has-dec-eq : (X : ℕ) → has-dec-eq (El X)
    El-has-dec-eq zero = λ ()
    El-has-dec-eq (succ X) (i₁ 0₁) (i₁ 0₁) = i₁ (refl (i₁ 0₁))
    El-has-dec-eq (succ X) (i₁ 0₁) (i₂ y) = i₂ (λ ())
    El-has-dec-eq (succ X) (i₂ x) (i₁ 0₁) = i₂ (λ ())
    El-has-dec-eq (succ X) (i₂ x) (i₂ y) with El-has-dec-eq X x y
    ... | i₁ x=y = i₁ (ap i₂ x=y)
    ... | i₂ x≠y = i₂ (λ p → x≠y (i₂-inj p))

    El-is-set : (X : ℕ) → is-set (El X)
    El-is-set X = hedberg (El X) (El-has-dec-eq X)

  open PathsInℕ using (reflect)


  is-finite : Type₀ → Type₁
  is-finite X = Σ ℕ (λ Y → ∥ X == El Y ∥)


  module IsFiniteIsProp where

    ∥reflect∥ = λ X Y → recTrunc ∥ X == Y ∥ (∣_∣ ∘ reflect X Y) identify
    ∥apsucc∥ = λ {X} {Y} → recTrunc (succ X == succ Y) (ap succ) (ℕ-is-set _ _)

    ∥+cncl𝟙l∥ : {ℓ : Level} → {X Y : Type ℓ} → ∥ 𝟙 + X == 𝟙 + Y ∥ → ∥ X == Y ∥
    ∥+cncl𝟙l∥ {X = X} {Y} = recTrunc (∥ X == Y ∥) (∣_∣ ∘ +cncl𝟙l {X = X} {Y}) identify

    is-finite-is-prop : (X : Type₀) → is-prop(is-finite X)
    is-finite-is-prop X (0 , p) (0 , q) = dpair= (refl 0 , identify _ _)
    is-finite-is-prop X (0 , p) (succ Z , q) =
      rec𝟘 _ (recTrunc 𝟘 (λ p → tpt id p (i₁ 0₁)) 𝟘-is-prop (∥!∥ q ∥◾∥ p))
    is-finite-is-prop X (succ Y , p) (0 , q) =
      rec𝟘 _ (recTrunc 𝟘 (λ p → tpt id p (i₁ 0₁)) 𝟘-is-prop (∥!∥ p ∥◾∥ q))
    is-finite-is-prop X (succ Y , p) (succ Z , q) =
      dpair= (∥apsucc∥ (∥reflect∥ Y Z (∥+cncl𝟙l∥ (∥!∥ p ∥◾∥ q))) , identify _ _)

  open IsFiniteIsProp using (is-finite-is-prop)

  finite-types-is-univ : is-univ-fib (p₁ {X = Type₀} {is-finite})
  finite-types-is-univ = pred-ext-is-univ is-finite is-finite-is-prop
