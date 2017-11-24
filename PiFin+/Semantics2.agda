{-# OPTIONS --without-K --rewriting #-}

module PiFin+.Semantics2 where

open import HoTT
open import PiFin+.Semantics0
open import PiFin+.Semantics1

2-paths-in-ℕ : (m n : ℕ) (p : m == n) → p == idp [ (λ x → x == n) ↓ p ]
2-paths-in-ℕ m .m idp = idp

2-paths-in-El : {n : ℕ} (x y : El n) (p : x == y) → p == idp [ (λ z → z == y) ↓ p ]
2-paths-in-El x .x idp = idp

abstract
  ⊔-unit-l-eqv : ∀ {ℓ} (X : Type ℓ) → ⊥ ⊔ X ≃ X
  ⊔-unit-l-eqv X = equiv f g f-g g-f
    where f : ⊥ ⊔ X → X
          f (inl ())
          f (inr x) = x
          g : X → ⊥ ⊔ X
          g = inr
          f-g : (b : X) → b == b
          f-g b = idp
          g-f : (a : ⊥ ⊔ X) → g (f a) == a
          g-f (inl ())
          g-f (inr x) = idp

⊔-unit-l : ∀ {ℓ} (X : Type ℓ) → ⊥ ⊔ X == X
⊔-unit-l = ua ∘ ⊔-unit-l-eqv

abstract
  ⊔-unit-r-eqv : ∀ {ℓ} (X : Type ℓ) → X ⊔ ⊥ ≃ X
  ⊔-unit-r-eqv X = equiv f g f-g g-f
    where f : X ⊔ ⊥ → X
          f (inl x) = x
          f (inr ())
          g : X → X ⊔ ⊥
          g = inl
          f-g : (b : X) → b == b
          f-g b = idp
          g-f : (a : X ⊔ ⊥) → g (f a) == a
          g-f (inl x) = idp
          g-f (inr ())

⊔-unit-r : ∀ {ℓ} (X : Type ℓ) → X ⊔ ⊥ == X
⊔-unit-r = ua ∘ ⊔-unit-r-eqv

abstract
  ⊔-assoc-eqv : ∀ {ℓ} (X Y Z : Type ℓ) → X ⊔ (Y ⊔ Z) ≃ (X ⊔ Y) ⊔ Z
  ⊔-assoc-eqv X Y Z = equiv f g f-g g-f
    where f : X ⊔ (Y ⊔ Z) → (X ⊔ Y) ⊔ Z
          f (inl x) = inl (inl x)
          f (inr (inl y)) = inl (inr y)
          f (inr (inr z)) = inr z
          g : (X ⊔ Y) ⊔ Z → X ⊔ (Y ⊔ Z)
          g (inl (inl x)) = inl x
          g (inl (inr y)) = inr (inl y)
          g (inr z) = inr (inr z)
          f-g : (b : (X ⊔ Y) ⊔ Z) → f (g b) == b
          f-g (inl (inl x)) = idp
          f-g (inl (inr y)) = idp
          f-g (inr z) = idp
          g-f : (a : X ⊔ (Y ⊔ Z)) → g (f a) == a
          g-f (inl x) = idp
          g-f (inr (inl y)) = idp
          g-f (inr (inr z)) = idp

⊔-assoc : ∀ {ℓ} (X Y Z : Type ℓ) → X ⊔ (Y ⊔ Z) == (X ⊔ Y) ⊔ Z
⊔-assoc X Y Z = ua (⊔-assoc-eqv X Y Z)

abstract
  ⊔-comm-eqv : ∀ {ℓ} (X Y : Type ℓ) → X ⊔ Y ≃ Y ⊔ X
  ⊔-comm-eqv X Y = equiv f g f-g g-f
    where f : X ⊔ Y → Y ⊔ X
          f (inl x) = inr x
          f (inr y) = inl y
          g : Y ⊔ X → X ⊔ Y
          g (inl y) = inr y
          g (inr x) = inl x
          f-g : (b : Y ⊔ X) → f (g b) == b
          f-g (inl y) = idp
          f-g (inr x) = idp
          g-f : (a : X ⊔ Y) → g (f a) == a
          g-f (inl x) = idp
          g-f (inr y) = idp

  ⊔-comm-eqv-inv : ∀ {ℓ} (X Y : Type ℓ) → ⊔-comm-eqv X Y == ⊔-comm-eqv Y X ⁻¹
  ⊔-comm-eqv-inv X Y = pair= p prop-has-all-paths-↓
    where p : –> (⊔-comm-eqv X Y) == <– (⊔-comm-eqv Y X)
          p = λ= λ { (inl x) → idp ; (inr x) → idp }

⊔-comm : ∀ {ℓ} (X Y : Type ℓ) → X ⊔ Y == Y ⊔ X
⊔-comm X Y = ua (⊔-comm-eqv X Y)

ide⁻¹ : ∀ {ℓ} {X : Type ℓ} → (ide X) ⁻¹ == ide X
ide⁻¹ {X = X} = pair= idp (prop-has-all-paths (is-equiv-inverse (idf-is-equiv X)) (idf-is-equiv X))

ua⁻¹ : ∀ {ℓ} {X Y : Type ℓ} (e : X ≃ Y) → ua (e ⁻¹) == ! (ua e)
ua⁻¹ e = equiv-induction (λ eq → ua (eq ⁻¹) == ! (ua eq))
                         (λ A → ((ap ua ide⁻¹) ∙ (ua-η idp)) ∙ (ap ! (! (ua-η idp)))) e

⊔-comm-inv : ∀ {ℓ} (X Y : Type ℓ) → ⊔-comm X Y == ! (⊔-comm Y X)
⊔-comm-inv X Y = (ap ua (⊔-comm-eqv-inv X Y)) ∙ ua⁻¹ (⊔-comm-eqv Y X)

El-+ : (m n : ℕ) → El (m + n) == (El m ⊔ El n)
El-+ O n = ! (⊔-unit-l (El n))
El-+ (S m) n = ap (λ X → ⊤ ⊔ X) (El-+ m n) ∙ ⊔-assoc ⊤ (El m) (El n)

`id : {m n : ℕ} (p : m == n) → El m == El n
`id = ap El

`id-coe-β : {n : ℕ} (p : n == n) (x : El n) → coe (`id p) x == x
`id-coe-β {n} p x = (ap (λ p → coe (ap El p) x) (prop-has-all-paths p idp))

`unite₊l : (n : ℕ) → El (0 + n) == El n
`unite₊l n = El-+ O n
           ∙ ⊔-unit-l (El n)

`unite₊l-coe-β : {n : ℕ} → (x : El n) → coe (`unite₊l n) x == x
`unite₊l-coe-β {O} ()
`unite₊l-coe-β {S n} x = ap (λ p → coe p x) (!-inv-l (⊔-unit-l (El (S n))))

`unite₊r : (n : ℕ) → El (n + 0) == El n
`unite₊r n = El-+ n 0
           ∙ ⊔-unit-r (El n)

`unite₊r-El : {n : ℕ} → El (n + 0) → El n
`unite₊r-El {n} x = –> (⊔-unit-r-eqv (El n)) (coe (El-+ n O) x)

`unite₊r-coe-β : {n : ℕ} → (x : El (n + 0)) → coe (`unite₊r n) x == `unite₊r-El x
`unite₊r-coe-β {n} x = coe-∙ (El-+ n O) (⊔-unit-r (El n)) x
                     ∙ coe-β (⊔-unit-r-eqv (El n)) (coe (El-+ n O) x)

`swap₊ : (m n : ℕ) → El (m + n) == El (n + m)
`swap₊ m n = El-+ m n
           ∙ ⊔-comm (El m) (El n)
           ∙ ! (El-+ n m)

`swap₊-El : {m n : ℕ} → El (m + n) → El (n + m)
`swap₊-El {m} {n} x = coe (! (El-+ n m)) (–> (⊔-comm-eqv (El m) (El n)) (coe (El-+ m n) x))

coe-∙∙ : ∀ {i} {A B C D : Type i} (p : A == B) (q : B == C) (r : C == D) (a : A)
       → coe (p ∙ q ∙ r) a == coe r (coe q (coe p a))
coe-∙∙ p q r a = (coe-∙ p (q ∙ r) a) ∙ (coe-∙ q r (coe p a))

`swap₊-coe-β : {m n : ℕ} → (x : El (m + n)) → coe (`swap₊ m n) x == `swap₊-El {m} {n} x
`swap₊-coe-β {m} {n} x = coe-∙∙ (El-+ m n) (⊔-comm (El m) (El n)) (! (El-+ n m)) x
                       ∙ ap (coe (! (El-+ n m)))
                            (coe-β (⊔-comm-eqv (El m) (El n))
                                   (coe (El-+ m n) x))

`assocl₊ : (m n o : ℕ) → El (m + (n + o)) == El ((m + n) + o)
`assocl₊ m n o = El-+ m (n + o)
               ∙ ap (λ X → El m ⊔ X) (El-+ n o)
               ∙ ⊔-assoc (El m) (El n) (El o)
               ∙ ! (ap (λ X → X ⊔ El o) (El-+ m n))
               ∙ ! (El-+ (m + n) o)

`assocl₊-El : {m n o : ℕ} → El (m + (n + o)) → El ((m + n) + o)
`assocl₊-El {m} {n} {o} x = coe (! (El-+ (m + n) o))
                              (coe (! (ap (λ X → X ⊔ El o) (El-+ m n)))
                                (–> (⊔-assoc-eqv (El m) (El n) (El o))
                                  (coe (ap (λ X → El m ⊔ X) (El-+ n o))
                                    (coe (El-+ m (n + o)) x))))

coe-∙∙∙∙ : ∀ {i} {A B C D E F : Type i} (p : A == B) (q : B == C) (r : C == D) (s : D == E) (t : E == F) (a : A)
         → coe (p ∙ q ∙ r ∙ s ∙ t) a == coe t (coe s (coe r (coe q (coe p a))))
coe-∙∙∙∙ p q r s t a = coe-∙∙ p q (r ∙ s ∙ t) a ∙ coe-∙∙ r s t (coe q (coe p a))

`assocl₊-El-β : {m n o : ℕ} → (x : El (m + (n + o))) → coe (`assocl₊ m n o) x == `assocl₊-El {m} {n} {o} x
`assocl₊-El-β {m} {n} {o} x = coe-∙∙∙∙ (El-+ m (n + o)) (ap (λ X → El m ⊔ X) (El-+ n o))
                                       (⊔-assoc (El m) (El n) (El o))
                                       (! (ap (λ X → X ⊔ El o) (El-+ m n))) (! (El-+ (m + n) o)) x
                            ∙ ap (coe ((! (El-+ (m + n) o))))
                                 (ap (coe ((! (ap (λ X → Coprod X (El o)) (El-+ m n)))))
                                     (coe-β (⊔-assoc-eqv (El m) (El n) (El o))
                                            (coe (ap (λ X → Coprod (El m) X) (El-+ n o))
                                                 (coe (El-+ m (n + o)) x))))

`swap₊² : (m n : ℕ) → El (m + n) == El (m + n)
`swap₊² m n = `swap₊ m n ∙ `swap₊ n m

`swap₊²=idp : (m n : ℕ) → `swap₊² m n == idp
`swap₊²=idp m n = path (El-+ m n) (⊔-comm (El m) (El n)) (⊔-comm (El n) (El m))
                       (El-+ n m) (⊔-comm-inv (El m) (El n))
  -- could be done with assoc but tedious
  where path : ∀ {ℓ} {X : Type ℓ} {a b c d : X}
             → (p : a == b) (q : b == c) (q' : c == b) (r : d == c)
             → (α : q == ! q')
             → (p ∙ q ∙ ! r) ∙ (r ∙ q' ∙ ! p) == idp
        path idp q q' idp α = ap (λ z → (q ∙ idp) ∙ z) (∙-unit-r q')
                            ∙ (ap (λ z → z ∙ q') (∙-unit-r q))
                            ∙ ((ap (λ z → z ∙ q') α) ∙ (!-inv-l q'))
