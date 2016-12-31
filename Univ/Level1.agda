{-# OPTIONS --type-in-type --without-K #-}

module Univ.Level1 where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function renaming (_∘_ to _○_)
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_)

open import Univ.Universe
open import Univ.Level0
  using    (𝟘; 𝟙; _⊕_; _⊗_)
  renaming (U to U₀; Fun to Fun₀;
            _∼_ to _∼₀_; refl∼ to refl∼₀; sym∼ to sym∼₀; trans∼ to trans∼₀;
            _≃_ to _≃₀_)

module MOD0 = Univ.Level0

data _⟷_ : U₀ → U₀ → Set where
  id⟷ :    {A : U₀} → A ⟷ A
  uniti₊r : {A : U₀} → A ⟷ (A ⊕ 𝟘)
  unite₊r : {A : U₀} → A ⊕ 𝟘 ⟷ A
  _◎_ :     {A B C : U₀} → (A ⟷ B) → (B ⟷ C) → (A ⟷ C)
  -- elided

! : {A B : U₀} → (A ⟷ B) → (B ⟷ A)
! unite₊r = uniti₊r
! uniti₊r = unite₊r
! id⟷ = id⟷
! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁

El : {A B : U₀} → (A ⟷ B) → Set
El {A} {B} _ = A ≃₀ B

sound : {A B : U₀} → (c : A ⟷ B) → El c
sound id⟷ = MOD0.id≃
sound uniti₊r = MOD0.sym≃ MOD0.A⊎⊥≃A
sound unite₊r = MOD0.A⊎⊥≃A
sound (c₁ ◎ c₂) = MOD0.trans≃ (sound c₁) (sound c₂)

Fun : {A B : U₀} → (c₁ c₂ : A ⟷ B) → Set
Fun {A} {B} _ _ =
  Σ[ F ∈ (Fun₀ A B → Fun₀ A B) ]
  Σ[ G ∈ (Fun₀ B A → Fun₀ B A) ]
  ((f : Fun₀ A B) → (F f ∼₀ f)) ×
  ((g : Fun₀ B A) → (G g ∼₀ g))

app : {A B : U₀} {c₁ c₂ : A ⟷ B} → Fun c₁ c₂ → El c₁ → El c₂
app (F , G , γ , δ) (f , MOD0.mkisequiv g α β) =
  F f ,
  MOD0.mkisequiv
    (G g)
    (trans∼₀ (MOD0.∼○ (δ g) (γ f)) α)
    (trans∼₀ (MOD0.∼○ (γ f) (δ g)) β)

idF : {A B : U₀} {c : A ⟷ B} → Fun c c
idF = (id , id , refl∼₀ , refl∼₀)

compose : {A B : U₀} {c₁ c₂ c₃ : A ⟷ B} → Fun c₁ c₂ → Fun c₂ c₃ → Fun c₁ c₃
compose (F₁ , G₁ , γ₁ , δ₁) (F₂ , G₂ , γ₂ , δ₂) =
  F₂ ○ F₁ ,
  G₂ ○ G₁ ,
  (λ f → trans∼₀ (γ₂ (F₁ f)) (γ₁ f)) ,
  (λ g → trans∼₀ (δ₂ (G₁ g)) (δ₁ g))

record _≡_ {A B : U₀} {c : A ⟷ B} (eq₁ eq₂ : El c) : Set where
  open MOD0.isequiv (proj₂ eq₁) renaming (g to g₁)
  open MOD0.isequiv (proj₂ eq₂) renaming (g to g₂)
  field
    f≡ : proj₁ eq₁ ∼₀ proj₁ eq₂
    g≡ : g₁ ∼₀ g₂

refl≡ : {A B : U₀} {c : A ⟷ B} (eq : El c) → _≡_ {c = c} eq eq
refl≡ (f , MOD0.mkisequiv g α β) =
  record {
    f≡ = MOD0.refl∼ f
  ; g≡ = MOD0.refl∼ g
  }

trans≡ : {A B : U₀} {c : A ⟷ B} {eq₁ eq₂ eq₃ : El c} →
         (_≡_ {c = c} eq₁ eq₂) → (_≡_ {c = c} eq₂ eq₃) →
         (_≡_ {c = c} eq₁ eq₃)
trans≡ (record { f≡ = f≡₁ ; g≡ = g≡₁ }) (record { f≡ = f≡₂ ; g≡ = g≡₂ }) =
  record {
    f≡ = MOD0.trans∼ f≡₁ f≡₂
  ; g≡ = MOD0.trans∼ g≡₁ g≡₂
  }

cong≡ : {A B : U₀} {c₁ c₂ : A ⟷ B} {eq₁ eq₂ : El c₁} →
      (f : Fun c₁ c₂) → _≡_ {c = c₁} eq₁ eq₂ →
      _≡_ {c = c₂} (app {c₁ = c₁} {c₂ = c₂} f eq₁) (app {c₁ = c₁} {c₂ = c₂} f eq₂)
cong≡ {eq₁ = f₁ , MOD0.mkisequiv g₁ α₁ β₁}
      {eq₂ = f₂ , MOD0.mkisequiv g₂ α₂ β₂}
      (F , G , γ , δ)
      (record { f≡ = f≡ ; g≡ = g≡ }) =
  record {
     f≡ = trans∼₀ (γ f₁) (trans∼₀ f≡ (sym∼₀ (γ f₂)))
   ; g≡ = trans∼₀ (δ g₁) (trans∼₀ g≡ (sym∼₀ (δ g₂)))
   }

_∼_ : {A B : U₀} {c₁ c₂ : A ⟷ B} → (f g : Fun c₁ c₂) → Set
_∼_ {c₁ = c₁} {c₂ = c₂} f g =
   (eq : El c₁) →
   _≡_ {c = c₂} (app {c₁ = c₁} {c₂ = c₂} f eq) (app {c₁ = c₁} {c₂ = c₂} g eq)

refl∼ : {A B : U₀} {c : A ⟷ B} → (f : Fun c c) →
        _∼_ {c₁ = c} {c₂ = c} f f
refl∼ {c = c} f eq = refl≡ (app {c₁ = c} {c₂ = c} f eq)

assoc-∘ : {A B : U₀} {c₁ c₂ c₃ c₄ : A ⟷ B} {f : Fun c₁ c₂} {g : Fun c₂ c₃} {h : Fun c₃ c₄} →
  _∼_ {c₁ = c₁} {c₄} (compose {c₁ = c₁} {c₂} {c₄} f (compose {c₁ = c₂} {c₃} {c₄} g h))
                     (compose {c₁ = c₁} {c₃} {c₄} (compose {c₁ = c₁} {c₂} {c₃} f g) h)
assoc-∘ = {!!}

record isequiv {A B : U₀} {c₁ c₂ : A ⟷ B}
       (f : Fun c₁ c₂) : Set where
  constructor mkisequiv
  field
    g : Fun c₂ c₁
    α : _∼_ {c₁ = c₂} {c₂ = c₂}
        (compose {c₁ = c₂} {c₂ = c₁} {c₃ = c₂} g f)
        (idF {c = c₂})
    β : _∼_ {c₁ = c₁} {c₂ = c₁}
        (compose {c₁ = c₁} {c₂ = c₂} {c₃ = c₁} f g)
        (idF {c = c₁})

_≃_ : {A B : U₀} → (c₁ c₂ : A ⟷ B) → Set
_≃_ {A} {B} c₁ c₂ = Σ (Fun c₁ c₂) (isequiv {c₁ = c₁} {c₂ = c₂})

id≃ : {A B : U₀} → (c : A ⟷ B) → c ≃ c
id≃ c = idF {c = c},
        mkisequiv
          (idF {c = c})
          (refl∼ {c = c} (idF {c = c}))
          (refl∼ {c = c} (idF {c = c}))

trans≃ : {A B : U₀} {c₁ c₂ c₃ : A ⟷ B} → (c₁ ≃ c₂) → (c₂ ≃ c₃) → (c₁ ≃ c₃)
trans≃ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}
   (f , mkisequiv f⁻ α₁ β₁) (g , mkisequiv g⁻ α₂ β₂) =
   compose {c₁ = c₁} {c₂ = c₂} {c₃ = c₃} f g ,
   mkisequiv (compose {c₁ = c₃} {c₂ = c₂} {c₃ = c₁} g⁻ f⁻)
   (λ eq₁ → {!!})
   (λ eq₂ → {!!})

Univ : (A B : U₀) → Universe
Univ A B = record
              { U = A ⟷ B
              ; El = λ _ → A ≃₀ B
              ; Fun = Fun
              ; _∼_ = λ { {c₁} {c₂} → _∼_ {c₁ = c₁} {c₂ = c₂}}
              ; _≡_ = λ { {c} → _≡_ {c = c}}
              ; _≃_ = _≃_
              ; SynCat = record
                           { id = λ {A} → idF {c = A}
                           ; _∘_ = λ {p} {q} {r} → compose {c₁ = r} {c₂ = q} {c₃ = p}
                           ; assoc = {!!}
                           ; identityˡ = {!!}
                           ; identityʳ = {!!}
                           ; equiv = {!!}
                           ; ∘-resp-≡ = {!!}
                           }
              ; ElFunc = {!!}
              }
