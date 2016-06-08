module 2D.Frac where

open import 2D.Types

open import Data.Sum
open import Data.Product
open import Data.Empty
open import Data.Unit

open import Categories.Category
open import Categories.Groupoid
open import Categories.Groupoid.Sum
open import Level hiding (lower)

open import Relation.Binary.PropositionalEquality
open import Function

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

open import Data.Nat as ℕ
open import Data.Integer as ℤ hiding (∣_∣)

infix 40 _^_

_^_ : {τ : U} → (p : τ ⟷ τ) → (k : ℤ) → (τ ⟷ τ)
p ^ (+ 0) = id⟷
p ^ (+ (suc k)) = p ◎ (p ^ (+ k))
p ^ -[1+ 0 ] = ! p
p ^ (-[1+ (suc k) ]) = (! p) ◎ (p ^ -[1+ k ])

assoc1 : {τ : U} → {p : τ ⟷ τ} → (m : ℕ) →
  (p ◎ (p ^ (+ m))) ⇔ ((p ^ (+ m)) ◎ p)
assoc1 ℕ.zero = trans⇔ idr◎l idl◎r
assoc1 (suc m) = trans⇔ (id⇔ ⊡ assoc1 m) assoc◎l

assoc1- : {τ : U} → {p : τ ⟷ τ} → (m : ℕ) →
  ((! p) ◎ (p ^ -[1+ m ])) ⇔ ((p ^ -[1+ m ]) ◎ (! p))
assoc1- ℕ.zero = id⇔
assoc1- (suc m) = trans⇔ (id⇔ ⊡ assoc1- m) assoc◎l

lower : {τ : U} {p : τ ⟷ τ} (m n : ℤ) → p ^ (m ℤ.+ n) ⇔ ((p ^ m) ◎ (p ^ n))
lower (+_ ℕ.zero) (+_ n) = idl◎r
lower (+_ ℕ.zero) (-[1+_] n) = idl◎r
lower (+_ (suc m)) (+_ n) = trans⇔ (id⇔ ⊡ lower (+ m) (+ n)) assoc◎l
lower {p = p} (+_ (suc m)) (-[1+_] ℕ.zero) =
  trans⇔ idr◎r (trans⇔ (id⇔ ⊡ linv◎r) (
  trans⇔ assoc◎l (2! (assoc1 m) ⊡ id⇔)))  -- p ^ ((m + 1) -1)
lower (+_ (suc m)) (-[1+_] (suc n)) = -- p ^ ((m + 1) -(1+1+n)
  trans⇔ (lower (+ m) (-[1+ n ])) (
  trans⇔ ((trans⇔ idr◎r (id⇔ ⊡ linv◎r))  ⊡ id⇔) (
  trans⇔ assoc◎r (trans⇔ (id⇔ ⊡ assoc◎r) (
  trans⇔ assoc◎l (2! (assoc1 m) ⊡ id⇔)))))
lower (-[1+_] m) (+_ ℕ.zero) = idr◎r
lower (-[1+_] ℕ.zero) (+_ (suc n)) = 2! (trans⇔ assoc◎l (
  trans⇔ (rinv◎l ⊡ id⇔) idl◎l))
lower (-[1+_] (suc m)) (+_ (suc n)) = -- p ^ (-(1+m) + (n+1))
  trans⇔ (lower (-[1+ m ]) (+ n)) (
    trans⇔ ((trans⇔ idr◎r (id⇔ ⊡ rinv◎r))  ⊡ id⇔) (
  trans⇔ assoc◎r (trans⇔ (id⇔ ⊡ assoc◎r) (
  trans⇔ assoc◎l ((2! (assoc1- m)) ⊡ id⇔)))))
lower (-[1+_] ℕ.zero) (-[1+_] n) = id⇔
lower (-[1+_] (suc m)) (-[1+_] n) = -- p ^ (-(1+1+m) - (1+n))
  trans⇔ (id⇔ ⊡ lower (-[1+ m ]) (-[1+ n ])) assoc◎l

record Perm {τ : U} (p : τ ⟷ τ) : Set where
  constructor perm
  field
    iter : ℤ
    p' : τ ⟷ τ
    p'⇔p^i : p' ⇔ p ^ iter

orderC : {τ : U} → (p : τ ⟷ τ) → Category _ _ _
orderC {τ} p = record {
     Obj = Perm p
   ; _⇒_ = λ { (perm i p₁ _) (perm j p₂ _) → p₁ ^ i ⇔ p₂ ^ j } 
   ; _≡_ = λ _ _ → ⊤ 
   ; id = id⇔ 
   ; _∘_ = λ α β → trans⇔ β α
   ; assoc = tt
   ; identityˡ = tt
   ; identityʳ = tt 
   ; equiv = record { refl = tt; sym = λ _ → tt; trans = λ _ _ → tt }
   ; ∘-resp-≡ = λ _ _ → tt  
   }
   where open Perm
   
1/orderC : (τ : U) → (τ ⟷ τ) → Category _ _ _
1/orderC τ pp = record { Obj = ⊤
                       ; _⇒_ = λ _ _ → Perm pp
                       ; _≡_ = λ { (perm m p _) (perm n q _) → p ⇔ q }
                       ; id = perm (+ 0) id⟷ id⇔
                       ; _∘_ = λ { (perm m p α) (perm n q β) →
                         perm (m ℤ.+ n) (p ◎ q) (trans⇔ (α ⊡ β) (2! (lower m n))) }
                       ; assoc = assoc◎r
                       ; identityˡ = idl◎l
                       ; identityʳ = idr◎l
                       ; equiv = record { refl = id⇔ ; sym = 2! ; trans = trans⇔ }
                       ; ∘-resp-≡ = _⊡_
                       }

!!⇔id : {t₁ t₂ : U} → (p : t₁ ⟷ t₂) → p ⇔ ! (! p)
!!⇔id _⟷_.unite₊l = id⇔
!!⇔id _⟷_.uniti₊l = id⇔
!!⇔id _⟷_.unite₊r = id⇔
!!⇔id _⟷_.uniti₊r = id⇔
!!⇔id _⟷_.swap₊ = id⇔
!!⇔id _⟷_.assocl₊ = id⇔
!!⇔id _⟷_.assocr₊ = id⇔
!!⇔id _⟷_.unite⋆l = id⇔
!!⇔id _⟷_.uniti⋆l = id⇔
!!⇔id _⟷_.unite⋆r = id⇔
!!⇔id _⟷_.uniti⋆r = id⇔
!!⇔id _⟷_.swap⋆ = id⇔
!!⇔id _⟷_.assocl⋆ = id⇔
!!⇔id _⟷_.assocr⋆ = id⇔
!!⇔id _⟷_.absorbr = id⇔
!!⇔id _⟷_.absorbl = id⇔
!!⇔id _⟷_.factorzr = id⇔
!!⇔id _⟷_.factorzl = id⇔
!!⇔id _⟷_.dist = id⇔
!!⇔id _⟷_.factor = id⇔
!!⇔id _⟷_.distl = id⇔
!!⇔id _⟷_.factorl = id⇔
!!⇔id id⟷ = id⇔
!!⇔id (p ◎ q) = !!⇔id p ⊡ !!⇔id q
!!⇔id (p _⟷_.⊕ q) = resp⊕⇔ (!!⇔id p) (!!⇔id q)
!!⇔id (p _⟷_.⊗ q) = resp⊗⇔ (!!⇔id p) (!!⇔id q)
!!⇔id (_⟷_.η p) = {!!}
!!⇔id (_⟷_.ε p) = {!!}

^⇔! : {τ : U} → {p : τ ⟷ τ} → (k : ℤ) → (p ^ (ℤ.- k)) ⇔ ! (p ^ k)
^⇔! (+_ ℕ.zero) = id⇔
-- need to dig deeper, as we end up negating
^⇔! (+_ (suc ℕ.zero)) = idl◎r
^⇔! (+_ (suc (suc n))) = trans⇔ (assoc1- n) (^⇔! (+ ℕ.suc n) ⊡ id⇔)
^⇔! {p = p} (-[1+_] ℕ.zero) = trans⇔ idr◎l (!!⇔id p)
^⇔! {p = p} (-[1+_] (suc n)) =
  trans⇔ (assoc1 (ℕ.suc n)) ((^⇔! -[1+ n ]) ⊡ (!!⇔id p))

⇔! : {τ₁ τ₂ : U} {p q : τ₁ ⟷ τ₂} → (p ⇔ q) → (! p ⇔ ! q)
⇔! assoc◎l = assoc◎r
⇔! assoc◎r = assoc◎l
⇔! idl◎l = idr◎l
⇔! idl◎r = idr◎r
⇔! idr◎l = idl◎l
⇔! idr◎r = idl◎r
⇔! id⇔ = id⇔
⇔! rinv◎l = linv◎l
⇔! rinv◎r = linv◎r
⇔! linv◎l = rinv◎l
⇔! linv◎r = rinv◎r
⇔! (trans⇔ q₁ q₂) = trans⇔ (⇔! q₁) (⇔! q₂)
⇔! (q₁ ⊡ q₂) = ⇔! q₂ ⊡ ⇔! q₁
⇔! (resp⊕⇔ q₁ q₂) = resp⊕⇔ (⇔! q₁) (⇔! q₂)
⇔! (resp⊗⇔ q₁ q₂) = resp⊗⇔ (⇔! q₁) (⇔! q₂)
⇔! ccc₁l = {!!}
⇔! ccc₁r = {!!}
⇔! ccc₂l = {!!}
⇔! ccc₂r = {!!}

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
⟦ 𝟘 ⟧ = _ , discreteG ⊥
⟦ 𝟙 ⟧ = _ , discreteG ⊤
⟦ t₁ ⊕ t₂ ⟧ with ⟦ t₁ ⟧ | ⟦ t₂ ⟧
... | (_ , G₁) | (_ , G₂) = _ , Sum G₁ G₂
⟦ t₁ ⊗ t₂ ⟧ with ⟦ t₁ ⟧ | ⟦ t₂ ⟧
... | (_ , G₁) | (_ , G₂) = _ , Product G₁ G₂
⟦ # p ⟧ = _ , orderG p
⟦ 1/# p ⟧ = _ , 1/orderG p

open import Rational+ as ℚ
open import 2D.Order

1÷_ : (n : ℕ) → {n≥1 : n ≥ 1} → ℚ
(1÷ (suc n)) {s≤s n≥1} = mkRational 1 (ℕ.suc n)

∣_∣ : U → ℚ
∣ 𝟘 ∣ = + 0 ÷ 1
∣ 𝟙 ∣ = + 1 ÷ 1
∣ t₁ ⊕ t₂ ∣ = ∣ t₁ ∣ ℚ.+ ∣ t₂ ∣
∣ t₁ ⊗ t₂ ∣ = ∣ t₁ ∣ ℚ.* ∣ t₂ ∣
∣ # p ∣ with order p
... | ord n n≥1 = mkRational n 1
∣ 1/# p ∣ with order p
... | ord n n≥1 = 1÷_ n {n≥1}
