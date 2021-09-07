{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

module Pi.Common.Misc where

open import HoTT hiding (_*_)

transport2 : ∀ {i j k} {A : Type i} {B : Type j} (C : A → B → Type k) {x1 x2 : A} {y1 y2 : B} (p : x1 == x2) (q : y1 == y2) → (C x1 y1 → C x2 y2)
transport2 C {x1} {x2} {y1} {y2} p q t = transport (uncurry C) (pair×= p q) t

transport2-equiv : ∀ {i j k} {A : Type i} {B : Type j} (C : A → B → Type k) {x1 x2 : A} {y1 y2 : B} (p : x1 == x2) (q : y1 == y2) → (C x1 y1 ≃ C x2 y2)
transport2-equiv C p q = transport-equiv (uncurry C) (pair×= p q)

infix  1 begin_

begin_ : {A : Type₀} -> {x y : A} → x == y → x == y
begin_ p = p

cong : {A B : Type₀} -> ∀ (f : A → B) {x y} → x == y → f x == f y
cong f p = ap f p

≡-sym : {A : Type₀} -> {p q : A} -> p == q -> q == p
≡-sym = !

≡-trans : {A : Type₀} -> {p q r : A} -> p == q -> q == r -> p == r
≡-trans = _∙_

idpp : {A : Type₀} -> {x : A} -> x == x
idpp {A} {x} = idp

data _⊎_ (A B : Type₀) : Type₀ where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

data BoolDec (A : Type₀) : Type₀ where
  yes : A -> BoolDec A
  no  : ¬ A -> BoolDec A

data SingletonWith {i} {A : Type i} (x : A) : Type i where
  _with==_ : (y : A) → x == y → SingletonWith x

inspect : ∀ {a} {A : Set a} (x : A) → SingletonWith x
inspect x = x with== idp


∘e-assoc : {A B C D : Type₀} → (ab : A ≃ B) → (bc : B ≃ C) → (cd : C ≃ D)
  → (cd ∘e (bc ∘e ab)) == (cd ∘e bc) ∘e ab
∘e-assoc ab bc cd = pair= idp (prop-has-all-paths _ _)

∘e-inv-r : {A B : Type₀} → (e : A ≃ B) → (e ∘e e ⁻¹) == (ide B)
∘e-inv-r e = pair= (λ= (λ x → <–-inv-r e x)) prop-has-all-paths-↓

∘e-unit-l : {A B : Type₀} → (e : A ≃ B) → ((ide B) ∘e e) == e
∘e-unit-l e = pair= (λ= (λ x → idp)) prop-has-all-paths-↓

∘e-inv-l : {A B : Type₀} → (e : A ≃ B) → (e ⁻¹ ∘e e) == (ide A)
∘e-inv-l e = pair= (λ= (λ x → <–-inv-l e x)) prop-has-all-paths-↓

-- post∘-equiv

cong≃ : {A B C : Type₀} → (B ≃ C) → (A ≃ B) ≃ (A ≃ C)
cong≃ bc = equiv f g f-g g-f
    where
    f : _
    f x = bc ∘e x --
    g : _
    g x = bc ⁻¹ ∘e x --
    f-g : _
    f-g x = ∘e-assoc x (bc ⁻¹) bc ∙ ap (λ e → e ∘e x) (∘e-inv-r bc) ∙ ∘e-unit-l x --
    g-f : _
    g-f x = ∘e-assoc x bc (bc ⁻¹) ∙ ap (λ e → e ∘e x) (∘e-inv-l bc) ∙ ∘e-unit-l x

double⁻¹ : {A B : Type₀} → (x : A ≃ B) → (x ⁻¹ ⁻¹) == x
double⁻¹ x = pair= idp (prop-has-all-paths _ _)

!≃ : {A B C D : Type₀} → (A ≃ B) ≃ (C ≃ D) → (B ≃ A) ≃ (D ≃ C)
!≃ (f , record { g = g ; f-g = f-g ; g-f = g-f ; adj = adj }) = equiv ff gg ff-gg gg-ff
    where
    ff : _
    ff x = f (x ⁻¹) ⁻¹
    gg : _
    gg x = g (x ⁻¹) ⁻¹
    ff-gg : _
    ff-gg x = (ap _⁻¹ (ap f (double⁻¹ (g (x ⁻¹)))) ∙ ap _⁻¹ (f-g (x ⁻¹))) ∙ double⁻¹ x
    gg-ff : _
    gg-ff x = (ap _⁻¹ (ap g (double⁻¹ (f (x ⁻¹)))) ∙ ap _⁻¹ (g-f (x ⁻¹))) ∙ double⁻¹ x

abstract
  e= : ∀ {i} {j} {X : Type i} {Y : Type j} {e₁ e₂ : Y ≃ X} → ((y : Y) → (–> e₁ y == –> e₂ y)) → e₁ == e₂
  e= h = pair= (λ= h) prop-has-all-paths-↓

  loop-η : ∀ {i} {X : Type i} {{_ : is-set X}} {x : X} → (p : x == x) → p == idp
  loop-η p = prop-has-all-paths p idp

  uip : ∀ {i} {X : Type i} {{_ : is-set X}} {x y : X} → (p q : x == y) → p == q
  uip p q = prop-has-all-paths p q

infixl 80 _*_
_*_ : ℕ → ℕ → ℕ
O * m = O
S n * m = m + (n * m)

{-# BUILTIN NATTIMES _*_ #-}

module _ {i} {A : Type i} {j} {R : Rel A j} where

  SetQuot-map : (f : A → A)
              → (f-cong : ∀ {a₁ a₂} → R a₁ a₂ → R (f a₁) (f a₂))
              → SetQuot R → SetQuot R
  SetQuot-map f f-cong = SetQuot-rec (q[_] ∘ f) (quot-rel ∘ f-cong)

  SetQuot-map-β : {f : A → A}
                → {f-cong : ∀ {a₁ a₂} → R a₁ a₂ → R (f a₁) (f a₂)}
                → (a : A) → SetQuot-map f f-cong q[ a ] == q[ f a ]
  SetQuot-map-β a = idp

  SetQuot-map2 : (f : A → A → A)
               → (R-is-refl : is-refl R)
               → (f-cong₂ : ∀ {a₁ a₂ b₁ b₂} → R a₁ a₂ → R b₁ b₂ → R (f a₁ b₁) (f a₂ b₂))
               → SetQuot R → SetQuot R → SetQuot R
  SetQuot-map2 f R-is-refl f-cong₂ =
    SetQuot-rec (λ a → SetQuot-rec (λ b → q[ f a b ])
                                   (λ p → quot-rel (f-cong₂ (R-is-refl a) p)))
                (λ p → λ= (SetQuot-elim (λ b → quot-rel (f-cong₂ p (R-is-refl b))) (λ r → prop-has-all-paths-↓)))

  SetQuot-map2-β : {f : A → A → A}
                 → {R-is-refl : is-refl R}
                 → {f-cong₂ : ∀ {a₁ a₂ b₁ b₂} → R a₁ a₂ → R b₁ b₂ → R (f a₁ b₁) (f a₂ b₂)}
                 → (a₁ a₂ : A) → SetQuot-map2 f R-is-refl f-cong₂ q[ a₁ ] q[ a₂ ] == q[ f a₁ a₂ ]
  SetQuot-map2-β a₁ a₂ = idp

reverse-++ : ∀ {i} {A : Type i} → (l₁ l₂ : List A) → reverse (l₁ ++ l₂) == (reverse l₂) ++ (reverse l₁)
reverse-++ nil l₂ = ! (++-unit-r _)
reverse-++ (x :: l₁) l₂ =
  let r = reverse-++ l₁ l₂
  in  ap (λ l → snoc l x) r ∙ ++-assoc (reverse l₂) (reverse l₁) (x :: nil)

module _ {i} {A : Type i} {j} (G : Group j) where
  private
    module G = Group G

  module _ (f : A → G.El) where

    Word-extendᴳ-:: : (x : PlusMinus A) (w : Word A)
                    → Word-extendᴳ G f (x :: w) == G.comp (PlusMinus-extendᴳ G f x) (Word-extendᴳ G f w)
    Word-extendᴳ-:: (inl x) nil = ! (G.unit-r (f x))
    Word-extendᴳ-:: (inr x) nil = ! (G.unit-r (G.inv (f x)))
    Word-extendᴳ-:: (inl x) (y :: w) = idp
    Word-extendᴳ-:: (inr x) (y :: w) = idp

module _ {i j k} {A : Type i} {B : Type j} {C : Type k}
         (f : A → B) (g : B → C) where

  map-∘ : {xs : List A} → map g (map f xs) == map (g ∘ f) xs
  map-∘ {xs = nil} = idp
  map-∘ {xs = x :: xs} = ap (g (f x) ::_) (map-∘ {xs = xs})

module _ {i} {A : Type i} where

  map-id : {xs : List A} → map (idf A) xs == xs
  map-id {xs = nil} = idp
  map-id {xs = x :: xs} = ap (x ::_) (map-id {xs = xs})

abstract
  fin= : {n : ℕ} {f g : Fin n} → f .fst == g .fst → f == g
  fin= p = pair= p prop-has-all-paths-↓


+-distr : ∀ {n m o} → (m * o) + (n * o) == (m + n) * o
+-distr {n} {O} {o} = idp
+-distr {n} {S m} {o} = 
    let r = +-distr {n} {m} {o}
    in  +-assoc o (m * o) (n * o) ∙ ap (o +_) r
