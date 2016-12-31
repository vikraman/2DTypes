{-# OPTIONS --type-in-type --without-K #-}

module Univ.Cats where

open import Relation.Binary

record IsCategory (Obj : Set) (Hom : Obj → Obj → Set) (Eq : ∀ {X Y} → Hom X Y → Hom X Y → Set) : Set where
  infixr 9 _∘_
  field
    id  : ∀ {A} → Hom A A
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

    assoc     : ∀ {A B C D} {f : Hom A B} {g : Hom B C} {h : Hom C D} → Eq ((h ∘ g) ∘ f) (h ∘ (g ∘ f))
    identityˡ : ∀ {A B} {f : Hom A B} → Eq (id ∘ f) f
    identityʳ : ∀ {A B} {f : Hom A B} → Eq (f ∘ id) f
    equiv     : ∀ {A B} → IsEquivalence (Eq {A} {B})
    ∘-resp-≡  : ∀ {A B C} {f h : Hom B C} {g i : Hom A B} → Eq f h → Eq g i → Eq (f ∘ g) (h ∘ i)

  open import Categories.Category using (Category)
  Cat : Category _ _ _
  Cat = record { Obj = Obj ; _⇒_ = Hom ; _≡_ = Eq
               ; id = id ; _∘_ = _∘_ ; assoc = assoc
               ; identityˡ = identityˡ ; identityʳ = identityʳ
               ; equiv = equiv ; ∘-resp-≡ = ∘-resp-≡ }

-- IsCategory should be resolved by instance arguments but isn't working
module _ {C D : Set} {HomC : C → C → Set} {HomD : D → D → Set}
         {EqC : ∀ {X Y} → HomC X Y → HomC X Y → Set} {EqD : ∀ {X Y} → HomD X Y → HomD X Y → Set}
         ⦃ CIsCat : IsCategory C HomC EqC ⦄ ⦃ DIsCat : IsCategory D HomD EqD ⦄ where

  private module C = IsCategory CIsCat
  private module D = IsCategory DIsCat

  record IsFunctor (f : C → D) : Set where
    field
      F : ∀ {X Y} → HomC X Y → HomD (f X) (f Y)

      identity : ∀ {X} → EqD (F (C.id {X})) (D.id)
      homomorphism : ∀ {X Y Z} {g : HomC Y Z} {h : HomC X Y}
                   → EqD (F (C._∘_ g h)) (D._∘_ (F g) (F h))
      F-resp-≡ : ∀ {X Y} {g h : HomC X Y} → EqC g h → EqD (F g) (F h)

    open import Categories.Functor using (Functor)
    Func : Functor C.Cat D.Cat
    Func = record { F₀ = f ; F₁ = F
                  ; identity = identity
                  ; homomorphism = homomorphism
                  ; F-resp-≡ = F-resp-≡ }
