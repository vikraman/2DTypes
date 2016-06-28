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
discreteC S = record { Obj = S
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

orderC : {τ : U} → (p : τ ⟷ τ) → Category _ _ _
orderC {τ} p = record {
     Obj = Iter p
   ; _⇒_ = _⇔#_
   ; _≡_ = _≡#_
   ; id  = id#p
   ; _∘_ = _∘#_
   ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → {!!}
   ; identityˡ = λ {_} {_} {m} → id#pˡ {m = m}
   ; identityʳ = λ {_} {_} {m} → id#pʳ {m = m}
   ; equiv = record
     { refl = λ {m} → refl# {m = m}
     ; sym = λ {m₁} {m₂} c → sym#p {m₁ = m₁} {m₂} c
     ; trans = λ {i} {j} {k} i≡j j≡k → trans#p {i = i} {j} {k} i≡j j≡k
   }
   ; ∘-resp-≡ = λ c₁ c₂ → {!!}
   }
   where
     open Sing
     open _⇔#_

open import Data.Integer as ℤ hiding (∣_∣)

1/orderC : (τ : U) → (τ ⟷ τ) → Category _ _ _
1/orderC τ pp = record { Obj = ⊤
                       ; _⇒_ = λ _ _ → Iter pp
                       ; _≡_ = λ { pp qq  → Iter.q pp ⇔ Iter.q qq }
                       ; id = < + 0 , Prim id⟷ , id⇔ >
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
    _⁻¹ = {!!} -- 2!
  ; iso = record {
        isoˡ = {!!}
      ; isoʳ = {!!}
      }
  }

1/orderG : {τ : U} → (p : τ ⟷ τ) → Groupoid (1/orderC τ p)
1/orderG {τ} p = record { _⁻¹ = λ { < i , q , eq > →
                        < ℤ.- i , ! q , ⇔! eq ● 2! (^⇔! {p = p} i) > }
                      ; iso = record { isoˡ = rinv◎l ; isoʳ = linv◎l }
                      }

postulate
  oneC : {τ : U} → (p : τ ⟷ τ) → Category _ _ _
  oneG : {τ : U} → (p : τ ⟷ τ) → Groupoid (oneC p)
  
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
∣ # p ∣ with order p
... | ord n n≥1 _ = n ÷1
∣ 1/# p ∣ with order p
... | ord n n≥1 _ = (1÷ n) {n≥1}
∣ 𝟙# p ∣ = + 1 ÷ 1 -- slight cheat, as this is really p / p.


------------------------------------------------------------------------------
-- Values

V : (T : U) → Set
V T = let ℂ , _ = ⟦ T ⟧
          open Category ℂ
      in Obj
