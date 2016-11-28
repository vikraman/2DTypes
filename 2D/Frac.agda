{-# OPTIONS --without-K #-}

module 2D.Frac where

open import 2D.Types

open import Data.Sum
open import Data.Product hiding (<_,_>;,_)
open import Data.Empty
open import Data.Unit

open import Categories.Category
import Categories.Product as C
import Categories.Coproduct as C
open import Categories.Groupoid
import Categories.Groupoid.Product as G
import Categories.Groupoid.Coproduct as G
open import Level hiding (lower)

open import Relation.Binary.PropositionalEquality
open import Function
open import 2D.Power
-- open import 2D.Sing
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

-- morphisms between p^i and p^j are proofs of equivalence
-- All proofs are equal
orderC : {τ : U} → (p : τ ⟷ τ) → Category _ _ _
orderC {τ} p = record {
     Obj = Iter p
   ; _⇒_ = λ p^i p^j → Iter.q p^i ⇔ Iter.q p^j
   ; _≡_ = λ _ _ → ⊤
   ; id  = id⇔
   ; _∘_ = flip _●_
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

-- special case of div construction when q = Prim id⟷
1/orderC : (τ : U) → (τ ⟷ τ) → Category _ _ _
1/orderC τ pp = record {
    Obj = Iter {τ} (Prim id⟷)
  ; _⇒_ = λ _ _ → Iter pp
  ; _≡_ = λ p q  → Iter.q p ⇔ Iter.q q
  ; id = zeroth pp
  ; _∘_ = _∘i_
  ; assoc = assoc◎r
  ; identityˡ = idl◎l
  ; identityʳ = idr◎l
  ; equiv = record { refl = id⇔ ; sym = 2! ; trans = _●_ }
  ; ∘-resp-≡ = _⊡_
  }

orderG : {τ : U} → (p : τ ⟷ τ) → Groupoid (orderC p)
orderG {τ} p = record {
    _⁻¹ = 2!
  ; iso = λ {a} {b} {f} → record {
        isoˡ = tt
      ; isoʳ = tt
      }
  }

1/orderG : {τ : U} → (p : τ ⟷ τ) → Groupoid (1/orderC τ p)
1/orderG {τ} p = record {
    _⁻¹ = inv
  ; iso = record { isoˡ = rinv◎l ; isoʳ = linv◎l }
  }

divC : {τ : U} → (p q : τ ⟷ τ) → Category _ _ _
divC {τ} p q = record {
    Obj = Iter p
  ; _⇒_ = λ s t → Σ[ iq ∈ Iter q ] ((Iter.q s ◎ Iter.q iq) ⇔ (Iter.q iq ◎ Iter.q t))
  ; _≡_ = λ { (iter₁ , _) (iter₂ , _) → Iter.q iter₁ ⇔ Iter.q iter₂ }
  ; id = λ {A} → zeroth q , idr◎l ● idl◎r
  ; _∘_ = λ { ( < j , q , αq > , pf₁)  ( < k , r , αr > , pf₂) →
                  ( < j , q , αq > ∘i < k , r , αr > ,
                  id⇔ ⊡ ( αq ⊡ αr ● comm-i-j j k) ● assoc◎l ●
                  (id⇔ ⊡ 2! αr ● pf₂) ⊡ id⇔ ● assoc◎r ● id⇔ ⊡ (id⇔ ⊡ 2! αq ● pf₁) ●
                  (assoc◎l ● (αr ⊡ αq ● comm-i-j k j ● 2! (αq ⊡ αr)) ⊡ id⇔)  ) }
  ; assoc = assoc◎r
  ; identityˡ = idl◎l
  ; identityʳ = idr◎l
  ; equiv = record { refl = id⇔ ; sym = 2! ; trans = _●_ }
  ; ∘-resp-≡ = _⊡_
  }

divG : {τ : U} → (p q : τ ⟷ τ) → Groupoid (divC p q)
divG {τ} p q = record {
    _⁻¹ = λ { {A} (q , pf) → inv q , (2! !aab⇔b ⊡ id⇔ ● assoc◎r) ●
            id⇔ {c = ! (Iter.q q)} ⊡ 2! pf ⊡ id⇔ {c = ! (Iter.q q)} ● id⇔ ⊡ (assoc◎r ● ab!b⇔a)  }
  ; iso = record { isoˡ = rinv◎l
                 ; isoʳ = linv◎l
                 }
  }

⟦_⟧ : (τ : U) → El τ
⟦ 𝟘 ⟧ = discreteC ⊥ , discreteG ⊥
⟦ 𝟙 ⟧ = discreteC ⊤ , discreteG ⊤
⟦ t₁ ⊕ t₂ ⟧ with ⟦ t₁ ⟧ | ⟦ t₂ ⟧
... | (C₁ , G₁) | (C₂ , G₂) = C.Coproduct C₁ C₂ , G.Coproduct G₁ G₂
⟦ t₁ ⊗ t₂ ⟧ with ⟦ t₁ ⟧ | ⟦ t₂ ⟧
... | (C₁ , G₁) | (C₂ , G₂) = C.Product C₁ C₂ , G.Product G₁ G₂
⟦ # p ⟧ = _ , orderG p
⟦ p // q ⟧ = _ , divG p q
⟦ q \\ p ⟧ = _ , divG p q

open import Data.Nat as ℕ
open import Rational+ as ℚ
open import 2D.Order

∣_∣ : U → ℚ
∣ 𝟘 ∣ = + 0 ÷ 1
∣ 𝟙 ∣ = + 1 ÷ 1
∣ t₁ ⊕ t₂ ∣ = ∣ t₁ ∣ ℚ.+ ∣ t₂ ∣
∣ t₁ ⊗ t₂ ∣ = ∣ t₁ ∣ ℚ.* ∣ t₂ ∣
∣ # p ∣ with orderPostulate p
... | ord n n≥1 _ = n ÷1
∣ p // q ∣ with orderPostulate p | orderPostulate q
... | ord i i≥1 _ | ord (ℕ.suc j) (ℕ.s≤s j≥1) _ = mkRational i (ℕ.suc j)
∣ p \\ q ∣ with orderPostulate p | orderPostulate q
... | ord i i≥1 _ | ord (ℕ.suc j) (ℕ.s≤s j≥1) _ = mkRational i (ℕ.suc j)


------------------------------------------------------------------------------
-- Values

V : (T : U) → Set
V T = Category.Obj (proj₁ ⟦ T ⟧)
