module 2D.Frac where

open import 2D.Types

open import Data.Sum
open import Data.Product hiding (_,_;<_,_>;,_)
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

open import Data.Integer as ℤ hiding (∣_∣)

record Iter {τ : U} (p : τ ⟷ τ) : Set where
  constructor <_,_,_>
  field
    iter : ℤ
    p' : τ ⟷ τ
    p'⇔p^i : p' ⇔ p ^ iter

orderC : {τ : U} → (p : τ ⟷ τ) → Category _ _ _
orderC {τ} p = record {
     Obj = Iter p
   ; _⇒_ = λ { (< i , p₁ , _>) (< j , p₂ , _>) → p₁ ⇔ p₂ }
   ; _≡_ = λ _ _ → ⊤
   ; id = id⇔
   ; _∘_ = λ α β → trans⇔ β α
   ; assoc = tt
   ; identityˡ = tt
   ; identityʳ = tt
   ; equiv = record { refl = tt; sym = λ _ → tt; trans = λ _ _ → tt }
   ; ∘-resp-≡ = λ _ _ → tt
   }
   where open Iter

1/orderC : (τ : U) → (τ ⟷ τ) → Category _ _ _
1/orderC τ pp = record { Obj = ⊤
                       ; _⇒_ = λ _ _ → Perm pp
                       ; _≡_ = λ { (perm m p _) (perm n q _) → p ⇔ q }
                       ; id = perm (+ 0) (Prim id⟷) id⇔
                       ; _∘_ = λ { (perm m p α) (perm n q β) →
                         perm (m ℤ.+ n) (p ◎ q) (trans⇔ (α ⊡ β) (2! (lower m n))) }
                       ; assoc = assoc◎r
                       ; identityˡ = idl◎l
                       ; identityʳ = idr◎l
                       ; equiv = record { refl = id⇔ ; sym = 2! ; trans = trans⇔ }
                       ; ∘-resp-≡ = _⊡_
                       }

^⇔! : {τ : U} → {p : τ ⟷ τ} → (k : ℤ) → (p ^ (ℤ.- k)) ⇔ ! (p ^ k)
^⇔! (+_ ℕ.zero) = id⇔
-- need to dig deeper, as we end up negating
^⇔! (+_ (suc ℕ.zero)) = idl◎r
^⇔! (+_ (suc (suc n))) = trans⇔ (assoc1- n) (^⇔! (+ ℕ.suc n) ⊡ id⇔)
^⇔! {p = p} (-[1+_] ℕ.zero) = trans⇔ idr◎l (!!⇔id p)
^⇔! {p = p} (-[1+_] (suc n)) =
  trans⇔ (assoc1 (ℕ.suc n)) ((^⇔! -[1+ n ]) ⊡ (!!⇔id p))

orderG : {τ : U} → (p : τ ⟷ τ) → Groupoid (orderC p)
orderG {τ} p = record {
    _⁻¹ = 2!
  ; iso = record {
        isoˡ = tt
      ; isoʳ = tt
      }
  }

1/orderG : {τ : U} → (p : τ ⟷ τ) → Groupoid (1/orderC τ p)
1/orderG {τ} p = record { _⁻¹ = λ { (perm i q eq) →
                        perm (ℤ.- i) (! q) (trans⇔ (⇔! eq) (2! (^⇔! {p = p} i)))}
                      ; iso = record { isoˡ = rinv◎l ; isoʳ = linv◎l }
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

open import Rational+ as ℚ
--open import 2D.Order

∣_∣ : U → ℚ
∣ 𝟘 ∣ = + 0 ÷ 1
∣ 𝟙 ∣ = + 1 ÷ 1
∣ t₁ ⊕ t₂ ∣ = ∣ t₁ ∣ ℚ.+ ∣ t₂ ∣
∣ t₁ ⊗ t₂ ∣ = ∣ t₁ ∣ ℚ.* ∣ t₂ ∣
∣ # p ∣ with order p
... | ord n n≥1 _ = n ÷1
∣ 1/# p ∣ with order p
... | ord n n≥1 _ = (1÷ n) {n≥1}


------------------------------------------------------------------------------
-- Values

V : (T : U) → Set
V T = let ℂ , _ = ⟦ T ⟧
          open Category ℂ
      in Σ[ v ∈ Obj ] (v ⇒ v)
