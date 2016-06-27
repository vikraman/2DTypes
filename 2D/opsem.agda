{-# OPTIONS --without-K #-}

module 2D.opsem where

open import Level using () renaming (zero to l0; suc to lsuc)
open import Universe using (Universe)
open import Data.Empty
open import Data.Bool
open import Data.Sum hiding ([_,_])
open import Data.Product
open import Function using (case_of_)
open import Categories.Category using (Category)
open import Categories.Groupoid using (Groupoid)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; suc; _≥_) renaming (_+_ to _ℕ+_)
open import Data.Integer
  using (ℤ; +_; -[1+_])
  renaming (-_ to ℤ-; suc to ℤsuc; _+_ to _ℤ+_)
open import Rational+ renaming (_+_ to _ℚ+_; _*_ to _ℚ*_)
  hiding (_≤_; _≤?_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; subst; cong; sym; cong₂)
open import Categories.Groupoid.Sum using () renaming (Sum to GSum)
open import Categories.Groupoid.Product using () renaming (Product to GProduct)

open import 2D.Types
open import 2D.Frac
open import 2D.Power
open import 2D.Order
open import 2D.Equality

-- Examples:

-- fractional values

fv : {τ : U} → (p : τ ⟷ τ) (i : ℤ) → V (1/# p)
fv p i = (perm i (Prim id⟷) (2! (id^i⇔id i)) , perm i (p ^ i) id⇔)

-- combinator values

cv : {τ : U} → (p : τ ⟷ τ) (i : ℤ) → V (# p)
cv p i = (perm i (p ^ i) id⇔ , id⇔)

-- left and right injections

inj₁/ : {T₁ T₂ : U} → V T₁ → V (T₁ ⊕ T₂)
inj₁/ (v , av) = (inj₁ v , av)

inj₂/ : {T₁ T₂ : U} → V T₂ → V (T₁ ⊕ T₂)
inj₂/ (v , av) = (inj₂ v , av)

-- pairing

[_,_] : {T₁ T₂ : U} → V T₁ → V T₂ → V (T₁ ⊗ T₂)
[ (v₁ , av₁) , (v₂ , av₂) ] = ((v₁ , v₂) , (av₁ , av₂))

--
BOOL : U
BOOL = 𝟙 ⊕ 𝟙

NOT : BOOL ⟷ BOOL
NOT = Prim swap₊

v₁ : V BOOL
v₁ = (inj₁ tt , refl)

v₂ v₃ : V (# NOT)
v₂ = cv NOT (+ 0)
v₃ = cv NOT (+ 1)

v₄ v₅ : V (1/# NOT)
v₄ = fv NOT (+ 0)
v₅ = fv NOT (+ 1)

v₆ v₇ : V (# NOT ⊕ BOOL)
v₆ = inj₁/ {T₁ = # NOT} {T₂ = BOOL} v₂
v₇ = inj₂/ {T₁ = # NOT} {T₂ = BOOL} v₁

v₈ : V (# NOT ⊗ BOOL)
v₈ = [_,_] {T₁ = # NOT} {T₂ = BOOL} v₂ v₁

v₉ : V (# NOT ⊗ 1/# NOT) -- mismatched pair
v₉ = [_,_] {T₁ = # NOT} {T₂ = 1/# NOT} v₂ v₅ 

------------------------------------------------------------------------------
-- evaluation of simple combinators forwards and backwards

prim : {T₁ T₂ : U} → (Prim⟷ T₁ T₂) → V T₁ → V T₂
prim unite₊l (inj₁ () , av)
prim unite₊l (inj₂ v , av) = (v , av) 
prim uniti₊l (v , av) = (inj₂ v , av)
prim unite₊r (inj₁ v , av) = (v , av)
prim unite₊r (inj₂ () , av)
prim uniti₊r (v , av) = (inj₁ v , av)
prim swap₊ (inj₁ v , av) = (inj₂ v , av)
prim swap₊ (inj₂ v , av) = (inj₁ v , av)
prim assocl₊ (inj₁ v , av) = (inj₁ (inj₁ v) , av)
prim assocl₊ ((inj₂ (inj₁ v)) , av) = (inj₁ (inj₂ v) , av)
prim assocl₊ ((inj₂ (inj₂ v)) , av) = (inj₂ v , av)
prim assocr₊ ((inj₁ (inj₁ v)) , av) = (inj₁ v , av)
prim assocr₊ ((inj₁ (inj₂ v)) , av) = (inj₂ (inj₁ v) , av)
prim assocr₊ (inj₂ v , av) = (inj₂ (inj₂ v) , av)
prim unite⋆l ((tt , v) , (_ , av)) = (v , av)
prim uniti⋆l (v , av) = (tt , v) , (refl , av)
prim unite⋆r ((v , tt) , (av , _)) = (v , av)
prim uniti⋆r (v , av) = ((v , tt) , (av , refl))
prim swap⋆ ((v₁ , v₂) , (av₁ , av₂)) = ((v₂ , v₁) , (av₂ , av₁))
prim assocl⋆ ((v₁ , (v₂ , v₃)) , (av₁ , (av₂ , av₃))) = (((v₁ , v₂) , v₃) , ((av₁ , av₂) , av₃))
prim assocr⋆ (((v₁ , v₂) , v₃) , ((av₁ , av₂) , av₃)) = ((v₁ , (v₂ , v₃)) , ((av₁ , (av₂ , av₃))))
prim absorbr ((v , _) , (av , _)) = (v , av)
prim absorbl ((_ , v) , (_ , av)) = (v , av)
prim factorzr (() , _)
prim factorzl (() , _)
prim dist ((inj₁ v₁ , v₃) , (av₁ , av₃)) = (inj₁ (v₁ , v₃) , (av₁ , av₃))
prim dist ((inj₂ v₂ , v₃) , (av₂ , av₃)) = (inj₂ (v₂ , v₃) , (av₂ , av₃))
prim factor (inj₁ (v₁ , v₃) , av) = ((inj₁ v₁ , v₃) , av)
prim factor (inj₂ (v₂ , v₃) , av) = ((inj₂ v₂ , v₃) , av)
prim distl ((v₃ , inj₁ v₁) , (av₃ , av₁)) = (inj₁ (v₃ , v₁) , (av₃ , av₁))
prim distl ((v₃ , inj₂ v₂) , (av₃ , av₂)) = (inj₂ (v₃ , v₂) , (av₃ , av₂))
prim factorl (inj₁ (v₃ , v₁) , av) = ((v₃ , inj₁ v₁) , av)
prim factorl (inj₂ (v₃ , v₂) , av) = ((v₃ , inj₂ v₂) , av)
prim id⟷ v = v

prim⁻¹ : {T₁ T₂ : U} → (Prim⟷ T₁ T₂) → V T₂ → V T₁
prim⁻¹ uniti₊l (inj₁ () , av)
prim⁻¹ uniti₊l (inj₂ v , av) = (v , av) 
prim⁻¹ unite₊l (v , av) = (inj₂ v , av)
prim⁻¹ uniti₊r (inj₁ v , av) = (v , av)
prim⁻¹ uniti₊r (inj₂ () , av)
prim⁻¹ unite₊r (v , av) = (inj₁ v , av)
prim⁻¹ swap₊ (inj₁ v , av) = (inj₂ v , av)
prim⁻¹ swap₊ (inj₂ v , av) = (inj₁ v , av)
prim⁻¹ assocr₊ (inj₁ v , av) = (inj₁ (inj₁ v) , av)
prim⁻¹ assocr₊ ((inj₂ (inj₁ v)) , av) = (inj₁ (inj₂ v) , av)
prim⁻¹ assocr₊ ((inj₂ (inj₂ v)) , av) = (inj₂ v , av)
prim⁻¹ assocl₊ ((inj₁ (inj₁ v)) , av) = (inj₁ v , av)
prim⁻¹ assocl₊ ((inj₁ (inj₂ v)) , av) = (inj₂ (inj₁ v) , av)
prim⁻¹ assocl₊ (inj₂ v , av) = (inj₂ (inj₂ v) , av)
prim⁻¹ uniti⋆l ((tt , v) , (_ , av)) = (v , av)
prim⁻¹ unite⋆l (v , av) = (tt , v) , (refl , av)
prim⁻¹ uniti⋆r ((v , tt) , (av , _)) = (v , av)
prim⁻¹ unite⋆r (v , av) = ((v , tt) , (av , refl))
prim⁻¹ swap⋆ ((v₁ , v₂) , (av₁ , av₂)) = ((v₂ , v₁) , (av₂ , av₁))
prim⁻¹ assocr⋆ ((v₁ , (v₂ , v₃)) , (av₁ , (av₂ , av₃))) = (((v₁ , v₂) , v₃) , ((av₁ , av₂) , av₃))
prim⁻¹ assocl⋆ (((v₁ , v₂) , v₃) , ((av₁ , av₂) , av₃)) = ((v₁ , (v₂ , v₃)) , ((av₁ , (av₂ , av₃))))
prim⁻¹ factorzl ((v , _) , (av , _)) = (v , av)
prim⁻¹ factorzr ((_ , v) , (_ , av)) = (v , av)
prim⁻¹ absorbl (() , _)
prim⁻¹ absorbr (() , _)
prim⁻¹ factor ((inj₁ v₁ , v₃) , (av₁ , av₃)) = (inj₁ (v₁ , v₃) , (av₁ , av₃))
prim⁻¹ factor ((inj₂ v₂ , v₃) , (av₂ , av₃)) = (inj₂ (v₂ , v₃) , (av₂ , av₃))
prim⁻¹ dist (inj₁ (v₁ , v₃) , av) = ((inj₁ v₁ , v₃) , av)
prim⁻¹ dist (inj₂ (v₂ , v₃) , av) = ((inj₂ v₂ , v₃) , av)
prim⁻¹ factorl ((v₃ , inj₁ v₁) , (av₃ , av₁)) = (inj₁ (v₃ , v₁) , (av₃ , av₁))
prim⁻¹ factorl ((v₃ , inj₂ v₂) , (av₃ , av₂)) = (inj₂ (v₃ , v₂) , (av₃ , av₂))
prim⁻¹ distl (inj₁ (v₃ , v₁) , av) = ((v₃ , inj₁ v₁) , av)
prim⁻¹ distl (inj₂ (v₃ , v₂) , av) = ((v₃ , inj₂ v₂) , av)
prim⁻¹ id⟷ v = v

prim◎prim⁻¹≡id : {T₁ T₂ : U} → (c : Prim⟷ T₁ T₂) → (v : V T₂) → prim c (prim⁻¹ c v) ≡ v
prim◎prim⁻¹≡id unite₊l (proj₁ , proj₂) = refl
prim◎prim⁻¹≡id uniti₊l (inj₁ () , proj₂)
prim◎prim⁻¹≡id uniti₊l (inj₂ y , proj₂) = refl
prim◎prim⁻¹≡id unite₊r x = refl
prim◎prim⁻¹≡id uniti₊r (inj₁ x , proj₂) = refl
prim◎prim⁻¹≡id uniti₊r (inj₂ () , proj₂)
prim◎prim⁻¹≡id swap₊ (inj₁ x , proj₂) = refl
prim◎prim⁻¹≡id swap₊ (inj₂ y , proj₂) = refl
prim◎prim⁻¹≡id assocl₊ (inj₁ (inj₁ x) , proj₂) = refl
prim◎prim⁻¹≡id assocl₊ (inj₁ (inj₂ y) , proj₂) = refl
prim◎prim⁻¹≡id assocl₊ (inj₂ y , proj₂) = refl
prim◎prim⁻¹≡id assocr₊ (inj₁ x , proj₂) = refl
prim◎prim⁻¹≡id assocr₊ (inj₂ (inj₁ x) , proj₂) = refl
prim◎prim⁻¹≡id assocr₊ (inj₂ (inj₂ y) , proj₂) = refl
prim◎prim⁻¹≡id unite⋆l x = refl
prim◎prim⁻¹≡id uniti⋆l ((tt , proj₂) , refl , proj₃) = refl
prim◎prim⁻¹≡id unite⋆r x = refl
prim◎prim⁻¹≡id uniti⋆r ((proj₁ , tt) , proj₃ , refl) = refl
prim◎prim⁻¹≡id swap⋆ x = refl
prim◎prim⁻¹≡id assocl⋆ x = refl
prim◎prim⁻¹≡id assocr⋆ x = refl
prim◎prim⁻¹≡id absorbr (() , _)
prim◎prim⁻¹≡id absorbl (() , _)
prim◎prim⁻¹≡id factorzr ((proj₁ , ()) , y)
prim◎prim⁻¹≡id factorzl ((() , proj₂) , proj₃ , proj₄)
prim◎prim⁻¹≡id dist (inj₁ (proj₁ , proj₂) , proj₃ , proj₄) = refl
prim◎prim⁻¹≡id dist (inj₂ y , proj₁ , proj₂) = refl
prim◎prim⁻¹≡id factor ((inj₁ x , proj₂) , proj₁ , proj₃) = refl
prim◎prim⁻¹≡id factor ((inj₂ y , proj₂) , proj₁ , proj₃) = refl
prim◎prim⁻¹≡id distl (inj₁ x , proj₁ , proj₂) = refl
prim◎prim⁻¹≡id distl (inj₂ y , proj₁ , proj₂) = refl
prim◎prim⁻¹≡id factorl ((proj₁ , inj₁ x) , proj₃ , proj₄) = refl
prim◎prim⁻¹≡id factorl ((proj₁ , inj₂ y) , proj₃ , proj₄) = refl
prim◎prim⁻¹≡id id⟷ x = refl

------------------------------------------------------------------------------
-- Contexts and machine states

-- Context T1 T2 T3 T₄ is a context missing T₂ ⇿ T₃ combinator and which
-- returns takes T₁ as original input and produce T₄ as final answer

data Context : U → U → U → U → Set where
  Empty : {T₁ T₂ : U} → Context T₁ T₁ T₂ T₂
  Fst : {T₀ T₁ T₂ T₃ T : U} →
    (C : Context T₀ T₁ T₃ T) → (P₂ : T₂ ⟷ T₃) → Context T₀ T₁ T₂ T
  Snd : {T₀ T₁ T₂ T₃ T : U} →
    (P₁ : T₁ ⟷ T₂) → (C : Context T₀ T₁ T₃ T) → Context T₀ T₂ T₃ T
  L× : {T₀ T₁ T₂ T₃ T₄ T : U} →
    (C : Context T₀ (T₁ ⊗ T₂) (T₃ ⊗ T₄) T) →
    (P₂ : T₂ ⟷ T₄) → V T₂ → Context T₀ T₁ T₃ T
  R× : {T₀ T₁ T₂ T₃ T₄ T : U} →
    (P₁ : T₁ ⟷ T₃) → V T₃ →
    (C : Context T₀ (T₁ ⊗ T₂) (T₃ ⊗ T₄) T) → Context T₀ T₂ T₄ T
  L+ : {T₀ T₁ T₂ T₃ T₄ T : U} →
    (C : Context T₀ (T₁ ⊕ T₂) (T₃ ⊕ T₄) T) → (P₂ : T₂ ⟷ T₄) → 
    Context T₀ T₁ T₃ T
  R+ : {T₀ T₁ T₂ T₃ T₄ T : U} →
    (P₁ : T₁ ⟷ T₃) → (C : Context T₀ (T₁ ⊕ T₂) (T₃ ⊕ T₄) T) → 
    Context T₀ T₂ T₄ T

data State : U → U → Set where
  Enter : {T₀ T₁ T₂ T : U} →
    (P : T₁ ⟷ T₂) → V T₁ → Context T₀ T₁ T₂ T → State T₀ T
  Exit : {T₀ T₁ T₂ T : U} →
    (P : T₁ ⟷ T₂) → V T₂ → Context T₀ T₁ T₂ T → State T₀ T

data Dir : Set where
  Fwd : Dir
  Bck : Dir

------------------------------------------------------------------------------
-- Evaluation

open import Relation.Nullary
open import Data.Nat.DivMod using (_mod_)
open import Data.Fin using (toℕ)
open import Relation.Nullary.Decidable

n≥1⇒n≠0 : ∀ {n} → n ≥ 1 → ¬ (n ≡ 0)
n≥1⇒n≠0 (Data.Nat.s≤s n≥1) ()

eqℕ : (n m : ℕ) → Bool
eqℕ ℕ.zero ℕ.zero = true
eqℕ ℕ.zero (suc m) = false
eqℕ (suc n) ℕ.zero = false
eqℕ (suc n) (suc m) = eqℕ n m

negModn : (n m : ℕ) → ℕ
negModn ℕ.zero m = ℕ.zero
negModn (suc n) m = (toℕ (m mod (suc n))) ℕ+ (suc n)

mmod : (m n : ℕ) → n ≥ 1 → ℕ
mmod m n n≥1 = toℕ (_mod_ m n {fromWitnessFalse (n≥1⇒n≠0 n≥1)})

_⇔?_ : {τ : U} {p : τ ⟷ τ} → (q r : Perm p) → Bool
_⇔?_ {p = p} (perm i q α) (perm j r γ) with order p
perm (+_ n₁) q α ⇔? perm (+_ n₂) r γ | ord n n≥1 p^n⇔id⟷ =
  eqℕ (mmod n₁ n n≥1) (mmod n₂ n n≥1)
perm (+_ n₁) q α ⇔? perm (-[1+_] n₂) r γ | ord n n≥1 p^n⇔id⟷ =
  eqℕ (mmod n₁ n n≥1) (mmod (negModn n n₂) n n≥1)
perm (-[1+_] n₁) q α ⇔? perm (+_ n₂) r γ | ord n n≥1 p^n⇔id⟷ =
  eqℕ (mmod (negModn n n₁) n n≥1) (mmod n₂ n n≥1)
perm (-[1+_] n₁) q α ⇔? perm (-[1+_] n₂) r γ | ord n n≥1 p^n⇔id⟷ =
  eqℕ (mmod n₁ n n≥1) (mmod n₂ n n≥1)

--------------------------------------------------

mutual
  {-# TERMINATING #-}
  𝓐𝓹 : {T₁ T₂ : U} → (T₁ ⟷ T₂) → V T₁ → V T₂
  𝓐𝓹 (_⟷_.Prim c) v = prim c v
  𝓐𝓹 (p ◎ q) v = 𝓐𝓹 q (𝓐𝓹 p v)
  𝓐𝓹 (p ⊕ q) (inj₁ v , av) =
    case (𝓐𝓹 p (v , av)) of λ { (v' , av') → (inj₁ v') , av' }
  𝓐𝓹 (p ⊕ q) (inj₂ v , av) =
    case (𝓐𝓹 q (v , av)) of λ { (v' , av') → (inj₂ v') , av' }
  𝓐𝓹 (p ⊗ q) ((v₁ , v₂) , (av₁ , av₂)) with ((𝓐𝓹 p (v₁ , av₁)) , (𝓐𝓹 q (v₂ , av₂)))
  𝓐𝓹 (p ⊗ q) ((v₁ , v₂) , av₁ , av₂) | (v₁' , av₁') , (v₂' , av₂') = (v₁' , v₂') , (av₁' , av₂')
  𝓐𝓹 (η+ p) (perm i q α , y) =
       ((perm i (p ^ i) id⇔) , (perm (ℤ- i ℤ+ i ℤ+ i) q {!!})) , (id⇔ , (perm i (p ^ i) id⇔))
    -- ((perm (+ 1) p idr◎r , perm i q α) , (id⇔ , perm (+ 1) p idr◎r))
  𝓐𝓹 (η- p) (pp , β) = ((pp , perm (+ 1) p idr◎r) , (perm (+ 1) p idr◎r , id⇔))
  𝓐𝓹 (ε+ p) ((perm i q α , perm k id δ) , (β , perm j r γ)) =
    (perm (i ℤ+ (ℤ- j) ℤ+ k) (p ^ (i ℤ+ (ℤ- j) ℤ+ k)) {!!}) , id⇔
--    if ((perm i q α) ⇔? (perm j r γ))
--       then (pp , id⇔)
--       else 𝓐𝓹 (ε+ p) ((perm i q α , pp) , (β , perm j r γ)) -- loop forever
  𝓐𝓹 (ε- p) ((pp , perm i q α) , (perm j r γ , β)) =
    if ((perm i q α) ⇔? (perm j r γ))
       then (pp , id⇔)
       else 𝓐𝓹 (ε- p) ((pp , perm i q α) , (perm j r γ , β))
  𝓐𝓹 foldSwap (inj₁ tt , av) = (perm (+ 0) (Prim id⟷) id⇔ , id⇔)
  𝓐𝓹 foldSwap (inj₂ tt , av) = (perm (+ 1) (Prim swap₊) idr◎r , id⇔)
  𝓐𝓹 unfoldSwap (v , av) =
    if (v ⇔? (perm (+ 0) (Prim id⟷) id⇔))
       then (inj₁ tt , refl)
       else (inj₂ tt , refl)
  𝓐𝓹 ap⟷ ((perm iter q α , v) , (av₁ , av₂)) =
    case (𝓐𝓹 q (v , av₂)) of λ { (v' , av₂') → (perm iter q α , v') , (av₁ , av₂') } 
  𝓐𝓹 ap⁻¹⟷ ((perm iter p' p'⇔p^i , v) , (av₁ , av₂)) with (𝓐𝓹⁻¹ p' (v , av₂))
  ... | v' , av₂' = (perm iter p' p'⇔p^i , v') , (av₁ , av₂')
  𝓐𝓹 contract (perm i _ _ , β) = tt , refl
  𝓐𝓹 expand (tt , refl) = perm (+ 0) (Prim id⟷) id⇔ , id⇔ -- this is not going to be reversible!
  𝓐𝓹 iap⟷ ((pp , v) , (perm iter q α , av)) =
    ((pp , v) , (perm iter q α , {!!}))
  𝓐𝓹 iap⁻¹⟷ ((pp , v) , (perm iter p' p'⇔p^i , av)) = {!!} 

  𝓐𝓹⁻¹ : {T₁ T₂ : U} → (T₁ ⟷ T₂) → V T₂ → V T₁
  𝓐𝓹⁻¹ (Prim c) v = prim⁻¹ c v
  𝓐𝓹⁻¹ (c₀ ◎ c₁) v = 𝓐𝓹⁻¹ c₀ (𝓐𝓹⁻¹ c₁ v)
  𝓐𝓹⁻¹ (c₀ ⊕ c₁) (inj₁ x , av) =  case (𝓐𝓹⁻¹ c₀ (x , av)) of λ {(v' , av') → inj₁ v' , av'}
  𝓐𝓹⁻¹ (c₀ ⊕ c₁) (inj₂ y , av) = case (𝓐𝓹⁻¹ c₁ (y , av)) of λ {(v' , av') → inj₂ v' , av'}
  𝓐𝓹⁻¹ (c₀ ⊗ c₁) ((x , y) , (av₁ , av₂)) =
    case (𝓐𝓹⁻¹ c₀ (x , av₁) , 𝓐𝓹⁻¹ c₁ (y , av₂)) of
        (λ { ((v₁ , av₁') , (v₂ , av₂')) → (v₁ , v₂) , (av₁' , av₂')})
  𝓐𝓹⁻¹ foldSwap (v , av) = 
    if (v ⇔? (perm (+ 0) (Prim id⟷) id⇔))
       then (inj₁ tt , refl)
       else (inj₂ tt , refl)
  𝓐𝓹⁻¹ unfoldSwap (inj₁ tt , refl) = (perm (+ 0) (Prim id⟷) id⇔ , id⇔)
  𝓐𝓹⁻¹ unfoldSwap (inj₂ tt , refl) = (perm (+ 1) (Prim swap₊) idr◎r , id⇔)
  𝓐𝓹⁻¹ ap⟷ ((perm iter q α , v) , (av₁ , av₂)) =
    case (𝓐𝓹⁻¹ q (v , av₂)) of (λ {(v' , av') → (perm iter q α , v') , (av₁ , av') })
  𝓐𝓹⁻¹ ap⁻¹⟷ ((perm i q α , v) , (av₁ , av₂)) = 
    case (𝓐𝓹 q (v , av₂)) of (λ { (v' , av') → ((perm i q α) , v') , (av₁ , av') })
  𝓐𝓹⁻¹ (η- c) ((v , _) , _) = v , id⇔ -- probably not the best
  𝓐𝓹⁻¹ (η+ c) ((perm i p' α , perm j id γ) , (β , perm k q ν)) =
    perm (i ℤ+ (ℤ- j) ℤ+ k) {!!} {!!} , {!!}
  𝓐𝓹⁻¹ (ε+ c) v = ((perm (+ 1) c idr◎r) , {!!}) , id⇔ , (perm (+ 1) c idr◎r)
  𝓐𝓹⁻¹ (ε- c) v = ({!!} , (perm (+ 1) c idr◎r)) , (perm (+ 1) c idr◎r) , id⇔
  𝓐𝓹⁻¹ (contract {t}) v = (perm (+ 0) (Prim id⟷) id⇔) , id⇔
  𝓐𝓹⁻¹ (expand {t}) v = tt , refl
  𝓐𝓹⁻¹ iap⟷ ((pp , v) , (perm iter q α , av)) = {!!} 
  𝓐𝓹⁻¹ iap⁻¹⟷ ((pp , v) , (perm iter p' p'⇔p^i , av)) = {!!} 

-- note how this uses 𝓐𝓹
cong≈ : (S T : U) → (c : S ⟷ T) (x y : V S) → [ S ] x ≈ y →  [ T ] (𝓐𝓹 c x) ≈ (𝓐𝓹 c y)
cong≈ S T (Prim c) x y eq = {!!}
cong≈ S T (c₀ ◎ c₁) x y eq = {!!}
cong≈ _ _ (_⊕_ {t} {_} {s} c₀ c₁) (inj₁ x , x⇒x) (inj₁ y , y⇒y) (inj₁≈ eq) =
  inj₁≈ (cong≈ t s c₀ (x , x⇒x) (y , y⇒y) eq)
cong≈ _ _ (c₀ ⊕ c₁) (inj₁ x , x⇒x) (inj₂ y , y⇒y) ()
cong≈ _ _ (c₀ ⊕ c₁) (inj₂ x , x⇒x) (inj₁ y , y⇒y) ()
cong≈ _ _ (c₀ ⊕ c₁) (inj₂ x , x⇒x) (inj₂ y , y⇒y) (inj₂≈ eq) = {!!}
cong≈ _ _ (_⊗_ {t₀} {t₁} {t₂} {t₃} c₀ c₁) ((v , w) , v⇒v , w⇒w) ((x , y) , x⇒x , y⇒y) (proj≈ v≈x w≈y) =
  proj≈ (cong≈ t₀ t₂ c₀ (v , v⇒v) (x , x⇒x) v≈x) (cong≈ t₁ t₃ c₁ (w , w⇒w) (y , y⇒y) w≈y)
cong≈ .(𝟙 ⊕ 𝟙) .(# (Prim swap₊)) foldSwap (_ , proj₂) (_ , proj₃) (inj₁≈ eq) = {!!}
cong≈ .(𝟙 ⊕ 𝟙) .(# (Prim swap₊)) foldSwap (_ , proj₂) (_ , proj₃) (inj₂≈ eq) = {!!}
cong≈ .(# (Prim swap₊)) .(𝟙 ⊕ 𝟙) unfoldSwap (proj₁ , proj₂) (proj₃ , proj₄) (#≈ x) = {!!}
cong≈ _ _ ap⟷ ((proj₁ , proj₅) , proj₂ , proj₆) ((proj₃ , proj₇) , proj₄ , proj₈) (proj≈ (#≈ x) eq₁) = {!!}
cong≈ _ _ ap⁻¹⟷ x y eq = {!!}
cong≈ _ _ (η- c) v w eq = {!!}
cong≈ _ _ (η+ c) v w eq = {!!}
cong≈ _ _ (ε+ c) v w eq = {!!}
cong≈ _ _ (ε- c) x y eq = {!!}
cong≈ .(# (Prim id⟷)) .𝟙 contract (proj₁ , proj₂) (proj₃ , proj₄) (#≈ x) = tt≈
cong≈ .𝟙 .(# (Prim id⟷)) expand (.tt , .refl) (.tt , .refl) tt≈ = #≈ id⇔
cong≈ _ _ iap⟷ _ _ _ = {!!}
cong≈ _ _ iap⁻¹⟷ _ _ _ = {!!}

fwd◎bwd≈id : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → (v : V T₂) → [ T₂ ] (𝓐𝓹 c (𝓐𝓹⁻¹ c v)) ≈ v
fwd◎bwd≈id {_} {T₂} (Prim x) v = ≡⇒≈[ T₂ ] (prim◎prim⁻¹≡id x v) 
fwd◎bwd≈id (c ◎ c₁) v = {!!} -- need cong≈ ?
fwd◎bwd≈id (c ⊕ c₁) (inj₁ x , x⇒x) = inj₁≈ (fwd◎bwd≈id c (x , x⇒x))
fwd◎bwd≈id (c ⊕ c₁) (inj₂ y , y⇒y) = inj₂≈ (fwd◎bwd≈id c₁ (y , y⇒y))
fwd◎bwd≈id (c ⊗ c₁) ((x , y) , (x⇒x , y⇒y)) =
    proj≈ (fwd◎bwd≈id c (x , x⇒x)) (fwd◎bwd≈id c₁ (y , y⇒y))
fwd◎bwd≈id foldSwap (perm i q α , β) = {!!}
fwd◎bwd≈id unfoldSwap (inj₁ tt , refl) = refl≈[ 𝟙 ⊕ 𝟙 ] (inj₁ tt , refl) 
fwd◎bwd≈id unfoldSwap (inj₂ tt , refl) = refl≈[ 𝟙 ⊕ 𝟙 ] (inj₂ tt , refl)
fwd◎bwd≈id (ap⟷ {t} {p}) ((perm i q β , t₁) , (α , r)) =
  proj≈ (refl≈[ # p ] (perm i q β , α) ) (fwd◎bwd≈id q (t₁ , r))
fwd◎bwd≈id (ap⁻¹⟷ {_} {p}) ((perm i q α , t₁) , (β , r)) =
  proj≈ (refl≈[ # p ] (perm i q α , β)) {!!} -- need to define mutually with other dir
fwd◎bwd≈id (η- c) ((pp , r) , (p , β)) = proj≈ (1/#≈ {!!} {!!} {!!}) (#≈ {!!}) -- false
fwd◎bwd≈id (η+ c) ((perm i r α , perm j _ _) , (β , perm k _ _)) = proj≈ (#≈ {!!}) {!!} -- false
fwd◎bwd≈id (iap⟷ {t} {p}) _ = {!!} 
fwd◎bwd≈id (iap⁻¹⟷ {_} {p}) _ = {!!}
fwd◎bwd≈id (ε+ c) v = {!!} -- warning: loops
fwd◎bwd≈id (ε- c) v = {!!} -- warning: loops
fwd◎bwd≈id contract (tt , refl) = tt≈
fwd◎bwd≈id (expand {t}) (perm i q α , β) = #≈ (trans⇔ (2! (id^i⇔id i)) (2! α))

-- Forward execution one step at a time
ap : {T₀ T : U} → (s : State T₀ T) → Dir × State T₀ T
-- primitives
ap (Enter (Prim c) v C) =
  Fwd , Exit (Prim c) (prim c v) C
-- sequential composition
ap (Enter (P₁ ◎ P₂) v C) =
  Fwd , Enter P₁ v (Fst C P₂)
ap (Exit P₁ v (Fst C P₂)) =
  Fwd , Enter P₂ v (Snd P₁ C) 
ap (Exit P₂ v₂ (Snd P₁ C)) =
  Fwd , Exit (P₁ ◎ P₂) v₂ C
-- choice composition
ap (Enter (P₁ ⊕ P₂) (inj₁ v₁ , av₁) C) =
  Fwd , Enter P₁ (v₁ , av₁) (L+ C P₂)
ap (Exit P₁ (v₁ , av) (L+ C P₂)) =
  Fwd , Exit (P₁ ⊕ P₂) (inj₁ v₁ , av) C  
ap (Enter (P₁ ⊕ P₂) (inj₂ v₂ , av₂) C) =
  Fwd , Enter P₂ (v₂ , av₂) (R+ P₁ C)
ap (Exit P₂ (v₂ , av) (R+ P₁ C)) =
  Fwd , Exit (P₁ ⊕ P₂) (inj₂ v₂ , av) C 
-- parallel composition
ap (Enter (P₁ ⊗ P₂) ((v₁ , v₂) , (av₁ , av₂)) C) =
  Fwd , Enter P₁ (v₁ , av₁) (L× C P₂ (v₂ , av₂))
ap (Exit P₁ v₁ (L× C P₂ v₂)) =
  Fwd , Enter P₂ v₂ (R× P₁ v₁ C)
ap (Exit P₂ (v₂ , av₂) (R× P₁ (v₁ , av₁) C)) =
  Fwd , Exit (P₁ ⊗ P₂) (((v₁ , v₂) , (av₁ , av₂))) C 
-- Swap
ap (Enter foldSwap (inj₁ tt , refl) C) =
  Fwd , Exit foldSwap (perm (+ 0) (Prim id⟷) id⇔ , id⇔) C 
ap (Enter foldSwap (inj₂ tt , refl) C) =
  Fwd , Exit foldSwap (perm (+ 1) (Prim swap₊) idr◎r , id⇔) C 
ap (Enter unfoldSwap (v , _) C) =
   if (v ⇔? (perm (+ 0) (Prim id⟷) id⇔))
      then Fwd , Exit unfoldSwap (inj₁ tt , refl) C
      else Fwd , Exit unfoldSwap (inj₂ tt , refl) C 
ap (Enter ap⟷ v C) = Fwd , Exit ap⟷ (𝓐𝓹 ap⟷ v) C
ap (Enter ap⁻¹⟷ v C) = Fwd , Exit ap⁻¹⟷ (𝓐𝓹 ap⁻¹⟷ v) C
ap (Enter iap⟷ v C) = {!!} 
ap (Enter iap⁻¹⟷ v C) = {!!} 
-- eta and epsilon
ap (Enter (η+ P) (pp , _) C) =
  Fwd , Exit (η+ P)
        ((perm (+ 1) P idr◎r , pp) , (id⇔ , perm (+ 1) P idr◎r))
        C
ap (Enter (η- P) (pp , _) C) =
  Fwd , Exit (η- P)
        ((pp , perm (+ 1) P idr◎r) , (perm (+ 1) P idr◎r , id⇔))
        C
ap (Enter (ε+ P) ((perm i q α , pp) , (β , perm j r γ)) C) =
   if ((perm i q α) ⇔? (perm j r γ))
     then Fwd , Exit (ε+ P) (pp , id⇔) C
     else Bck , Enter (ε+ P) ((perm i q α , pp) , (β , perm j r γ)) C
ap (Enter (ε- P) ((pp , perm i q α) , (perm j r γ , β)) C) =
   if ((perm i q α) ⇔? (perm j r γ))
     then Fwd , Exit (ε- P) (pp , id⇔) C
     else Bck , Enter (ε- P) (((pp , perm i q α) , (perm j r γ , β))) C
ap (Enter (contract {t}) v C) = {!!}
ap (Enter (expand {t}) v C) = {!!}
-- done
ap (Exit P v Empty) = Fwd , Exit P v Empty

-- Reverse execution one step at a time

ap⁻¹ : {T₀ T : U} → State T₀ T → Dir × State T₀ T
-- primitives
ap⁻¹ (Exit (Prim c) v C) =
  Bck , Enter (Prim c) (prim⁻¹ c v) C
-- sequential composition
ap⁻¹ (Exit (P₁ ◎ P₂) v C) =
  Bck , Exit P₂ v (Snd P₁ C)
ap⁻¹ (Enter P₂ v₂ (Snd P₁ C)) =
  Bck , Exit P₁ v₂ (Fst C P₂)
ap⁻¹ (Enter P₁ v (Fst C P₂)) =
  Bck , Enter (P₁ ◎ P₂) v C 
-- choice composition
ap⁻¹ (Exit (P₁ ⊕ P₂) (inj₁ v₁ , av) C) =
  Bck , Exit P₁ (v₁ , av) (L+ C P₂) 
ap⁻¹ (Enter P₁ (v₁ , av) (L+ C P₂)) =
  Bck , Enter (P₁ ⊕ P₂) (inj₁ v₁ , av) C  
ap⁻¹ (Exit (P₁ ⊕ P₂) (inj₂ v₂ , av) C) =
  Bck , Exit P₂ (v₂ , av) (R+ P₁ C) 
ap⁻¹ (Enter P₂ (v₂ , av) (R+ P₁ C)) =
  Bck , Enter (P₁ ⊕ P₂) (inj₂ v₂ , av) C 
-- parallel composition
ap⁻¹ (Exit (P₁ ⊗ P₂) ((v₁ , v₂) , (av₁ , av₂)) C) =
  Bck , Exit P₂ (v₂ , av₂) (R× P₁ (v₁ , av₁) C)
ap⁻¹ (Enter P₂ (v₂ , av₂) (R× P₁ (v₁ , av₁) C)) =
  Bck , Exit P₁ (v₁ , av₁) (L× C P₂ (v₂ , av₂))
ap⁻¹ (Enter P₁ (v₁ , av₁) (L× C P₂ (v₂ , av₂))) =
  Bck , Enter (P₁ ⊗ P₂) (((v₁ , v₂) , (av₁ , av₂))) C 
-- Swap
ap⁻¹ (Exit foldSwap (v , _) C) =
     if (v ⇔? (perm (+ 0) (Prim id⟷) id⇔))
        then Bck , Enter foldSwap (inj₁ tt , refl) C
        else Fwd , Enter foldSwap (inj₂ tt , refl) C  
ap⁻¹ (Exit unfoldSwap (inj₁ tt , _) C) = Bck , Enter unfoldSwap (perm (+ 0) (Prim id⟷) id⇔ , id⇔) C 
ap⁻¹ (Exit unfoldSwap (inj₂ tt , _) C) = Bck , Enter unfoldSwap (perm (+ 1) (Prim swap₊) idr◎r , id⇔) C 
ap⁻¹ (Exit ap⟷ v C) = Bck , Enter ap⟷ (𝓐𝓹 ap⁻¹⟷ v) C 
ap⁻¹ (Exit ap⁻¹⟷ v C) = Bck , Enter ap⟷ (𝓐𝓹 ap⟷ v) C  
ap⁻¹ (Exit iap⟷ v C) = {!!} 
ap⁻¹ (Exit iap⁻¹⟷ v C) = {!!}
-- eta and epsilon
ap⁻¹ (Exit (ε+ P) (pp , _) C) =
  -- if forward execution proceeded past ε with p^5 we backtrack using p; this may cause
  -- that we never reach a fixed point even if one exists
  Bck , Enter (ε+ P)
        ((perm (+ 1) P idr◎r , pp) , (id⇔ , perm (+ 1) P idr◎r))
        C
ap⁻¹ (Exit (ε- P) (pp , _) C) =
  Bck , Enter (ε- P)
        ((pp , perm (+ 1) P idr◎r) , (perm (+ 1) P idr◎r , id⇔))
        C
ap⁻¹ (Exit (η+ P) ((perm i q α , pp) , (β , perm j r γ)) C) =
  -- what should really happen is that η counts how many times backtracking reaches here
  -- and after it exhausts all the choice, it lets execution proceed backwards for other
  -- ηs upstream to get a chance at revisiting their choices
   Fwd , Exit (η+ P)
             ( ((perm (ℤsuc i) (P ◎ q)
               (trans⇔ (id⇔ ⊡ α)
               (trans⇔ (idr◎r ⊡ id⇔)
               (2! (lower {p = P} (+ 1) i))))) , pp)
             , (id⇔ , (perm (ℤsuc i) (P ◎ q)
               (trans⇔ (id⇔ ⊡ α)
               (trans⇔ (idr◎r ⊡ id⇔)
               (2! (lower {p = P} (+ 1) i)))))))
             C
ap⁻¹ (Exit (η- P) ((pp , perm i q α) , (perm j r γ , β)) C) =
--   if ((perm i q α) ⇔? (perm j r γ))
--     then Bck , Enter (η- P) (tt , refl) C
--     else Fwd , Exit (η- P) (((tt , perm i q α) , (perm j r γ , β))) C
 Fwd , Exit (η- P)
             ( (pp , (perm (ℤsuc i) (P ◎ q)
               (trans⇔ (id⇔ ⊡ α)
               (trans⇔ (idr◎r ⊡ id⇔)
               (2! (lower {p = P} (+ 1) i))))))
             , ((perm (ℤsuc i) (P ◎ q)
               (trans⇔ (id⇔ ⊡ α)
               (trans⇔ (idr◎r ⊡ id⇔)
               (2! (lower {p = P} (+ 1) i))))) , id⇔))
             C
ap⁻¹ (Exit (contract {t}) v C) = {!!}
ap⁻¹ (Exit (expand {t}) v C) = {!!}

-- done 
ap⁻¹ (Enter P v Empty) = Bck , Enter P v Empty 

-- big step execution

postulate
  IMPOSSIBLE : {T : U} → V T

{-# NON_TERMINATING #-}

mutual 
  loopFwd : {T₀ T : U} → (s : State T₀ T) → V T
  loopFwd s with ap s 
  ... | Fwd , (Exit _ v Empty) = v
  ... | Fwd , s' = loopFwd s' 
  ... | Bck , s' = loopBck s' 

  loopBck : {T₀ T : U} → State T₀ T → V T
  loopBck s with ap⁻¹ s
  ... | Bck , (Enter {T₀} {.T₀} {T} {.T} p v Empty) = IMPOSSIBLE {T}
  ... | Bck , s' = loopBck s'
  ... | Fwd , s' = loopFwd s'

------------------------------------------------------------------------------
-- Examples and thoughts

eval : {t₁ t₂ : U} → (c : t₁ ⟷ t₂) → V t₁ → V t₂
eval c v = loopFwd (Enter c v Empty)

-- Credit card example

cc : # NOT ⟷ # NOT
cc = Prim (uniti⋆l {BOOL}) ◎ (expand ⊗ Prim id⟷) ◎
     (((η+ NOT) ⊗ Prim id⟷) ◎
     ((Prim assocr⋆ ◎
     ((Prim id⟷ ⊗ Prim swap⋆) ◎
     ((Prim id⟷ ⊗ (ε+ NOT)) ◎
     (Prim id⟷ ⊗ contract) ◎ Prim (unite⋆r {BOOL}))))))

t0 = loopFwd (Enter cc (cv NOT (+ 0)) Empty)
-- evals to:
-- perm (+ 2)
--      (Prim swap₊ ◎ Prim swap₊)
--      (trans⇔ (id⇔ ⊡ idr◎r)
--      (trans⇔ (idr◎r ⊡ id⇔) (trans⇔ assoc◎r (id⇔ ⊡ idl◎l))))
-- , id⇔
t1 = loopFwd (Enter cc (cv NOT (+ 1)) Empty)
-- evals to: perm (+ 1) (Prim swap₊) idr◎r , id⇔
t2 = loopBck (Enter cc (cv NOT (+ 0)) Empty)
-- evals to: perm (+ 0) (Prim id⟷) id⇔ , id⇔
t3 = loopBck (Enter cc (cv NOT (+ 1)) Empty)
-- evals to: perm (+ 1) (Prim swap₊ ◎ Prim id⟷) id⇔ , id⇔

-- HOF

FALSE TRUE : V BOOL
FALSE = (inj₁ tt , refl)
TRUE = (inj₂ tt , refl)

cnot : BOOL ⊗ BOOL ⟷ BOOL ⊗ BOOL
cnot = (foldSwap {𝟙} ⊗ Prim id⟷) ◎ ap⟷ ◎ (unfoldSwap ⊗ Prim id⟷)

testcnot : V (BOOL ⊗ BOOL)
testcnot = eval cnot ([_,_] {BOOL} {BOOL} TRUE FALSE)

{-
%% -- Trivial implementation of eta/epsilon that does
%% -- type check (see below).  Might be interesting to figure out why
%% -- that is:
%% -- ap/ (η {τ} {p}) (v , av) =
%% --   (((+ 0) , (p , id⇔)) , tt) , (id⇔ , ((+ 0) , (p , id⇔)))
%% -- ap/ ε (v , av) = tt , refl
-}

{--
ap⁻¹ (Exit (η+ P) ((perm i q α , tt) , (β , perm j r γ)) C) =
  if (q ⇔? r)
  then Bck , Enter (η+ P) (tt , refl) C
  else Fwd , Exit (η+ P)
             ( ((perm (ℤsuc i) (P ◎ q)
               (trans⇔ (id⇔ ⊡ α)
               (trans⇔ (idr◎r ⊡ id⇔)
               (2! (lower {p = P} (+ 1) i))))) , tt)
             , (id⇔ , (perm (ℤsuc i) (P ◎ q)
               (trans⇔ (id⇔ ⊡ α)
               (trans⇔ (idr◎r ⊡ id⇔)
               (2! (lower {p = P} (+ 1) i)))))))
             C
ap⁻¹ (Exit (η- P) ((tt , perm i q α) , (perm j r γ , β)) C) =
  if (q ⇔? r)
  then Bck , Enter (η- P) (tt , refl) C
  else Fwd , Exit (η- P)
             ( (tt , (perm (ℤsuc i) (P ◎ q)
               (trans⇔ (id⇔ ⊡ α)
               (trans⇔ (idr◎r ⊡ id⇔)
               (2! (lower {p = P} (+ 1) i))))))
             , ((perm (ℤsuc i) (P ◎ q)
               (trans⇔ (id⇔ ⊡ α)
               (trans⇔ (idr◎r ⊡ id⇔)
               (2! (lower {p = P} (+ 1) i))))) , id⇔))
             C
--}

------------------------------------------------------------------------------

-- things that have to be true for all of this to hold together
--- bwd◎fwd≡id :

------------------------------------------------------------------------------
-- tau // p

postulate
  𝓐𝓹⇔≡ : {T₁ T₂ : U} {p q : T₁ ⟷ T₂} → p ⇔ q → (v : V T₁) → 𝓐𝓹 p v ≡ 𝓐𝓹 q v
  𝓐𝓹≡ : {T₁ T₂ : U} {p : T₁ ⟷ T₂} (v : V T₂) → 𝓐𝓹 p (𝓐𝓹 (! p) v) ≡ v
  𝓐𝓹!≡ : {T₁ T₂ : U} {p : T₁ ⟷ T₂} (v : V T₁) → 𝓐𝓹 (! p) (𝓐𝓹 p v) ≡ v

p!p⇒C : {τ : U} (p : τ ⟷ τ) → Category _ _ _ 
p!p⇒C {τ} p = record {
     Obj = V τ
   ; _⇒_ = λ v₁ v₂ → (Σ[ j ∈ ℤ ] (𝓐𝓹 (p ^ j) v₁) ≡ v₂)
   ; _≡_ = λ { (j , _) (j' , _) → ((p ^ j) ⇔ (p ^ j')) }
   ; id = ((+ 0) , refl)
   ; _∘_ = λ { {v₁} {v₂} {v₃} (j₂ , a₂₃) (j₁ , a₁₂) →
               (j₁ ℤ+ j₂ , trans (𝓐𝓹⇔≡ (lower j₁ j₂) v₁)
                          (trans (cong (λ v → 𝓐𝓹 (p ^ j₂) v) a₁₂)
                                 a₂₃)) } -- ((j₁ + j₂ , compose≡ j₁ j₂ a₁₂ a₂₃) , (k₁ + k₂ , compose≡ k₁ k₂ b₁₂ b₂₃)) }
   ; assoc = (λ { {A} {B} {C} {D} {j₁ , α₁} {j₂ , α₂} {j₃ , α₃} →
                trans⇔ (lower j₁ (j₂ ℤ+ j₃))
               (trans⇔ (id⇔ ⊡ lower j₂ j₃)
               (trans⇔ assoc◎l
               (trans⇔ (2! (lower j₁ j₂) ⊡ id⇔)
                       (2! (lower (j₁ ℤ+ j₂) j₃))))) })
   ; identityˡ = λ { {A} {B} {j₁ , α₁} → trans⇔ (lower j₁ (+ 0)) idr◎l } 
   ; identityʳ = λ { {A} {B} {j₁ , α₁} → trans⇔ (lower (+ 0) j₁) idl◎l } 
   ; equiv = record { refl = id⇔ ; sym = 2! ; trans = trans⇔ } 
   ; ∘-resp-≡ = λ { {A} {B} {C} {jf , αf} {jh , αh} {jg , αg} {ji , αi}
                    p^jf⇔p^jh p^jg⇔p^ji → trans⇔ (lower jg jf)
                                         (trans⇔ (p^jg⇔p^ji ⊡ p^jf⇔p^jh)
                                                 (2! (lower ji jh))) }
   }

j+-j : (j : ℤ) → j ℤ+ (ℤ- j) ≡ (+ 0)
j+-j (+_ ℕ.zero) = refl
j+-j (+_ (suc n)) = j+-j -[1+ n ]
j+-j (-[1+_] ℕ.zero) = refl
j+-j (-[1+_] (suc n)) = j+-j -[1+ n ]

-j+j : (j : ℤ) → (ℤ- j) ℤ+ j ≡ (+ 0)
-j+j (+_ ℕ.zero) = refl
-j+j (+_ (suc n)) = -j+j -[1+ n ]
-j+j (-[1+_] ℕ.zero) = refl
-j+j (-[1+_] (suc n)) = -j+j -[1+ n ]

p⇒G : {τ : U} (p : τ ⟷ τ) → Groupoid (p!p⇒C p)
p⇒G {τ} p = record
  { _⁻¹ =
    λ { {v₁} {v₂} (j , α) → (ℤ- j) , (trans (cong (λ v → 𝓐𝓹 (p ^ (ℤ- j)) v) (sym α))
                                     (trans (𝓐𝓹⇔≡ (2! (lower j (ℤ- j))) v₁)
                                            (cong (λ z → 𝓐𝓹 (p ^ z) v₁) (j+-j j)))) }
  ; iso = λ { {A} {B} {j , α}
        → record { isoˡ = subst (λ n → p ^ n ⇔ Prim id⟷) (sym (j+-j j)) id⇔
                 ; isoʳ = subst (λ n → p ^ n ⇔ Prim id⟷) (sym (-j+j j)) id⇔ } }
  }



------------------------------------------------------------------------------
