{-# OPTIONS --without-K #-}

module 2D.Frac where

open import 2D.Types

open import Data.Sum
open import Data.Product hiding (<_,_>;,_)
open import Data.Empty
open import Data.Unit

open import Categories.Category
import Categories.Sum as C
import Categories.Product as C
open import Categories.Groupoid
import Categories.Groupoid.Sum as G
import Categories.Groupoid.Product as G
open import Level hiding (lower)

open import Relation.Binary.PropositionalEquality
open import Function
open import 2D.Power
open import 2D.Sing
open import 2D.Iter
open import 2D.ProgMorphisms

discreteC : Set → Category zero zero zero
discreteC S = record {
    Obj = S
  ; _⇒_ = _≡_
  ; _≡_ = λ _ _ → ⊤
  ; id = refl
  ; _∘_ = flip trans
  ; assoc = tt
  ; identityˡ = tt
  ; identityʳ = tt
  ; equiv = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
  ; ∘-resp-≡ = λ _ _ → tt
  }

discreteG : (S : Set) → Groupoid (discreteC S)
discreteG S = record { _⁻¹ = sym
                     ; iso = record { isoˡ = tt ; isoʳ = tt }
                     }

-- morphisms between p^i and p^j are proofs of equivalence, but
-- phrased as one being the inverse of the other.
-- All proofs are equal
orderC : {τ : U} → (p : τ ⟷ τ) → Category _ _ _
orderC {τ} p = record {
     Obj = Iter p
   ; _⇒_ = λ p^i p^j → Iter.q p^i ◎ ! (Iter.q p^j) ⇔ Prim id⟷
   ; _≡_ = λ _ _ → ⊤
   ; id  = linv◎l
   ; _∘_ = λ B!C A!B → 2! (2! A!B ● idr◎r ● id⇔ ⊡ (2! B!C) ●
           assoc◎l ● (assoc◎r ● id⇔ ⊡ rinv◎l ● idr◎l) ⊡ id⇔ )
   ; assoc = tt
   ; identityˡ = tt
   ; identityʳ = tt
   ; equiv = record
     { refl = tt
     ; sym = λ _ → tt
     ; trans = λ _ _ → tt
     }
   ; ∘-resp-≡ = λ _ _ → tt
   }

open import Data.Integer as ℤ hiding (∣_∣)

1/orderC : (τ : U) → (τ ⟷ τ) → Category _ _ _
1/orderC τ pp = record {
    Obj = Sing pp
  ; _⇒_ = λ _ _ → Iter pp -- unlike in Val, here we skip the 'trivial' proof
  ; _≡_ = λ { pp qq  → Iter.q pp ⇔ Iter.q qq }
  ; id = zeroth pp
  ; _∘_ = λ { < m , p , α > < n , q , β > →
              < m ℤ.+ n , p ◎ q , α ⊡ β ● 2! (lower m n) > }
  ; assoc = assoc◎r
  ; identityˡ = idl◎l
  ; identityʳ = idr◎l
  ; equiv = record { refl = id⇔ ; sym = 2! ; trans = _●_ }
  ; ∘-resp-≡ = _⊡_
  }

orderG : {τ : U} → (p : τ ⟷ τ) → Groupoid (orderC p)
orderG {τ} p = record {
    _⁻¹ = λ {_} {B} pf → !!⇔id (Iter.q B) ⊡ id⇔ ● ⇔! pf
  ; iso = λ {a} {b} {f} → record {
        isoˡ = tt
      ; isoʳ = tt
      }
  }

1/orderG : {τ : U} → (p : τ ⟷ τ) → Groupoid (1/orderC τ p)
1/orderG {τ} p = record {
    _⁻¹ = λ { < i , q , eq > → < ℤ.- i , ! q , ⇔! eq ● 2! (^⇔! {p = p} i) > }
  ; iso = record { isoˡ = rinv◎l ; isoʳ = linv◎l }
  }

oneC : {τ : U} → (p : τ ⟷ τ) → Category _ _ _
oneC {τ} p = record {
    Obj = Iter p
  ; _⇒_ = λ _ _ → Iter p
  ; _≡_ = λ iter₁ iter₂ → Iter.q iter₁ ⇔ Iter.q iter₂
  ; id = zeroth p
  ; _∘_ = λ { < m , p , α >  < n , q , β > →
              < m ℤ.+ n , p ◎ q , α ⊡ β ● 2! (lower m n) > }
  ; assoc = assoc◎r
  ; identityˡ = idl◎l
  ; identityʳ = idr◎l
  ; equiv = record { refl = id⇔ ; sym = 2! ; trans = _●_ }
  ; ∘-resp-≡ = _⊡_
  }

oneG : {τ : U} → (p : τ ⟷ τ) → Groupoid (oneC p)
oneG {τ} p = record {
    _⁻¹ = λ { (< i , q , eq >) → < ℤ.- i , ! q , ⇔! eq ● 2! (^⇔! {p = p} i) > }
  ; iso = record { isoˡ = rinv◎l
                 ; isoʳ = linv◎l
                 }
  }

⟦_⟧ : (τ : U) → El τ
⟦ 𝟘 ⟧ = discreteC ⊥ , discreteG ⊥
⟦ 𝟙 ⟧ = discreteC ⊤ , discreteG ⊤
⟦ t₁ ⊕ t₂ ⟧ with ⟦ t₁ ⟧ | ⟦ t₂ ⟧
... | (C₁ , G₁) | (C₂ , G₂) = C.Sum C₁ C₂ , G.Sum G₁ G₂
⟦ t₁ ⊗ t₂ ⟧ with ⟦ t₁ ⟧ | ⟦ t₂ ⟧
... | (C₁ , G₁) | (C₂ , G₂) = C.Product C₁ C₂ , G.Product G₁ G₂
⟦ # p ⟧ = _ , orderG p
⟦ 1/# p ⟧ = _ , 1/orderG p
⟦ 𝟙# p ⟧ = _ , oneG p

open import Rational+ as ℚ
open import 2D.Order

∣_∣ : U → ℚ
∣ 𝟘 ∣ = + 0 ÷ 1
∣ 𝟙 ∣ = + 1 ÷ 1
∣ t₁ ⊕ t₂ ∣ = ∣ t₁ ∣ ℚ.+ ∣ t₂ ∣
∣ t₁ ⊗ t₂ ∣ = ∣ t₁ ∣ ℚ.* ∣ t₂ ∣
∣ # p ∣ with orderPostulate p
... | ord n n≥1 _ = n ÷1
∣ 1/# p ∣ with orderPostulate p
... | ord n n≥1 _ = (1÷ n) {n≥1}
∣ 𝟙# p ∣ = + 1 ÷ 1 -- slight cheat, as this is really order p / order p.


------------------------------------------------------------------------------
-- Values

V : (T : U) → Set
V T = Category.Obj (proj₁ ⟦ T ⟧)
