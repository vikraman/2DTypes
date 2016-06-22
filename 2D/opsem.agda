{-# OPTIONS --without-K #-}

module 2D.opsem where

open import Level using () renaming (zero to l0; suc to lsuc)
open import Universe using (Universe)
open import Data.Empty
open import Data.Bool
open import Data.Sum hiding ([_,_])
open import Data.Product
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
  using (_≡_; refl; trans; subst)
open import Categories.Groupoid.Sum using () renaming (Sum to GSum)
open import Categories.Groupoid.Product using () renaming (Product to GProduct)

open import 2D.Types
open import 2D.Frac
open import 2D.Order

------------------------------------------------------------------------------
-- Values

V : (T : U) → Set
V T = let ℂ , _ = ⟦ T ⟧
          open Category ℂ
      in Σ[ v ∈ Obj ] (v ⇒ v)

-- Examples:

-- fractional values

fv : {τ : U} → (p : τ ⟷ τ) (i : ℤ) → V (1/# p)
fv p i = (tt , perm i (p ^ i) id⇔)

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


------------------------------------------------------------------------------
-- Contexts and machine states

-- Context T1 T2 T3 is a context missing T1 ⇿ T2 combinator and which
-- returns T3 as final answer

data Context : U → U → U → Set where
  Empty : {T : U} → Context T T T
  Fst : {T₁ T₂ T₃ T : U} →
    (C : Context T₁ T₃ T) → (P₂ : T₂ ⟷ T₃) → Context T₁ T₂ T
  Snd : {T₁ T₂ T₃ T : U} →
    (P₁ : T₁ ⟷ T₂) → (C : Context T₁ T₃ T) → Context T₂ T₃ T
  L× : {T₁ T₂ T₃ T₄ T : U} →
    (C : Context (T₁ ⊗ T₂) (T₃ ⊗ T₄) T) →
    (P₂ : T₂ ⟷ T₄) → V T₂ → Context T₁ T₃ T
  R× : {T₁ T₂ T₃ T₄ T : U} →
    (P₁ : T₁ ⟷ T₃) → V T₃ →
    (C : Context (T₁ ⊗ T₂) (T₃ ⊗ T₄) T) → Context T₂ T₄ T
  L+ : {T₁ T₂ T₃ T₄ T : U} →
    (C : Context (T₁ ⊕ T₂) (T₃ ⊕ T₄) T) → (P₂ : T₂ ⟷ T₄) → 
    Context T₁ T₃ T
  R+ : {T₁ T₂ T₃ T₄ T : U} →
    (P₁ : T₁ ⟷ T₃) → (C : Context (T₁ ⊕ T₂) (T₃ ⊕ T₄) T) → 
    Context T₂ T₄ T

data State : U → Set where
  Enter : {T₁ T₂ T : U} →
    (P : T₁ ⟷ T₂) → V T₁ → Context T₁ T₂ T → State T
  Exit : {T₁ T₂ T : U} →
    (P : T₁ ⟷ T₂) → V T₂ → Context T₁ T₂ T → State T

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

{-# NON_TERMINATING #-}
𝓐𝓹 : {T₁ T₂ : U} → (T₁ ⟷ T₂) → V T₁ → V T₂
𝓐𝓹 (_⟷_.Prim c) v = prim c v
𝓐𝓹 (p ◎ q) v = 𝓐𝓹 q (𝓐𝓹 p v)
𝓐𝓹 (p ⊕ q) (inj₁ v , av) with (𝓐𝓹 p (v , av))
𝓐𝓹 (p ⊕ q) (inj₁ v , av) | v' , av' = (inj₁ v') , av'
𝓐𝓹 (p ⊕ q) (inj₂ v , av) with (𝓐𝓹 q (v , av))
𝓐𝓹 (p ⊕ q) (inj₂ v , av) | v' , av' = (inj₂ v') , av'
𝓐𝓹 (p ⊗ q) ((v₁ , v₂) , (av₁ , av₂)) with ((𝓐𝓹 p (v₁ , av₁)) , (𝓐𝓹 q (v₂ , av₂)))
𝓐𝓹 (p ⊗ q) ((v₁ , v₂) , av₁ , av₂) | (v₁' , av₁') , (v₂' , av₂') = (v₁' , v₂') , (av₁' , av₂')
𝓐𝓹 (η+ p) v = ((perm (+ 1) p idr◎r , tt) , (id⇔ , perm (+ 1) p idr◎r))
𝓐𝓹 (η- p) v = ((tt , perm (+ 1) p idr◎r) , (perm (+ 1) p idr◎r , id⇔))
𝓐𝓹 (ε+ p) ((perm i q α , tt) , (β , perm j r γ)) =
  if ((perm i q α) ⇔? (perm j r γ))
     then (tt , refl)
     else 𝓐𝓹 (ε+ p) ((perm i q α , tt) , (β , perm j r γ)) -- loop forever
𝓐𝓹 (ε- p) ((tt , perm i q α) , (perm j r γ , β)) =
  if ((perm i q α) ⇔? (perm j r γ))
     then (tt , refl)
     else 𝓐𝓹 (ε- p) ((tt , perm i q α) , (perm j r γ , β))
𝓐𝓹 foldSwap (inj₁ tt , av) = (perm (+ 0) (Prim id⟷) id⇔ , id⇔)
𝓐𝓹 foldSwap (inj₂ tt , av) = (perm (+ 1) (Prim swap₊) idr◎r , id⇔)
𝓐𝓹 unfoldSwap (v , av) =
  if (v ⇔? (perm (+ 0) (Prim id⟷) id⇔))
     then (inj₁ tt , refl)
     else (inj₂ tt , refl)
𝓐𝓹 ap⟷ ((perm iter p' p'⇔p^i , v) , (av₁ , av₂)) with (𝓐𝓹 p' (v , av₂))
𝓐𝓹 ap⟷ ((perm iter p' p'⇔p^i , v) , (av₁ , av₂)) | v' , av₂' = (perm iter p' p'⇔p^i , v') , (av₁ , av₂')
𝓐𝓹 ap⁻¹⟷ ((perm iter p' p'⇔p^i , v) , (av₁ , av₂)) with (𝓐𝓹 (p' ^ -[1+ 0 ]) (v , av₂))
... | v' , av₂' = (perm iter p' p'⇔p^i , v') , (av₁ , av₂')

-- Forward execution one step at a time

ap : {T : U} → (s : State T) → Dir × State T
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
-- eta and epsilon
ap (Enter (η+ P) (tt , _) C) =
  Fwd , Exit (η+ P)
        ((perm (+ 1) P idr◎r , tt) , (id⇔ , perm (+ 1) P idr◎r))
        C
ap (Enter (η- P) (tt , _) C) =
  Fwd , Exit (η- P)
        ((tt , perm (+ 1) P idr◎r) , (perm (+ 1) P idr◎r , id⇔))
        C
ap (Enter (ε+ P) ((perm i q α , tt) , (β , perm j r γ)) C) =
   if ((perm i q α) ⇔? (perm j r γ))
     then Fwd , Exit (ε+ P) (tt , refl) C
     else Bck , Enter (ε+ P) ((perm i q α , tt) , (β , perm j r γ)) C
ap (Enter (ε- P) ((tt , perm i q α) , (perm j r γ , β)) C) =
   if ((perm i q α) ⇔? (perm j r γ))
     then Fwd , Exit (ε- P) (tt , refl) C
     else Bck , Enter (ε- P) (((tt , perm i q α) , (perm j r γ , β))) C
-- done
ap (Exit P v Empty) = Fwd , Exit P v Empty

-- Reverse execution one step at a time

ap⁻¹ : {T : U} → State T → Dir × State T
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
-- eta and epsilon
ap⁻¹ (Exit (ε+ P) (tt , _) C) =
  -- if forward execution proceeded past ε with p^5 we backtrack using p; this may cause
  -- that we never reach a fixed point even if one exists
  Bck , Enter (ε+ P)
        ((perm (+ 1) P idr◎r , tt) , (id⇔ , perm (+ 1) P idr◎r))
        C
ap⁻¹ (Exit (ε- P) (tt , _) C) =
  Bck , Enter (ε- P)
        ((tt , perm (+ 1) P idr◎r) , (perm (+ 1) P idr◎r , id⇔))
        C
ap⁻¹ (Exit (η+ P) ((perm i q α , tt) , (β , perm j r γ)) C) =
  -- what should really happen is that η counts how many times backtracking reaches here
  -- and after it exhausts all the choice, it lets execution proceed backwards for other
  -- ηs upstream to get a chance at revisiting their choices
   Fwd , Exit (η+ P)
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
--   if ((perm i q α) ⇔? (perm j r γ))
--     then Bck , Enter (η- P) (tt , refl) C
--     else Fwd , Exit (η- P) (((tt , perm i q α) , (perm j r γ , β))) C
 Fwd , Exit (η- P)
             ( (tt , (perm (ℤsuc i) (P ◎ q)
               (trans⇔ (id⇔ ⊡ α)
               (trans⇔ (idr◎r ⊡ id⇔)
               (2! (lower {p = P} (+ 1) i))))))
             , ((perm (ℤsuc i) (P ◎ q)
               (trans⇔ (id⇔ ⊡ α)
               (trans⇔ (idr◎r ⊡ id⇔)
               (2! (lower {p = P} (+ 1) i))))) , id⇔))
             C
-- done 
ap⁻¹ (Enter P v Empty) = Bck , Enter P v Empty 

-- big step execution

{-# NON_TERMINATING #-}

mutual 
  loopFwd : {T : U} → (s : State T) → V T
  loopFwd s with ap s 
  ... | Fwd , (Exit _ v Empty) = v
  ... | Fwd , s' = loopFwd s' 
  ... | Bck , s' = loopBck s'

  loopBck : {T : U} → State T → V T
  loopBck s with ap⁻¹ s
  ... | Bck , (Enter _ v Empty) = v
  ... | Bck , s' = loopBck s'
  ... | Fwd , s' = loopFwd s'

-- Useful to run globally:
-- fwd : {T₁ T₂ T : U} → (T₁ ⟷ T₂) → V T₁ → V T
-- fwd {_} {_} {t} c v = loopFwd  (Enter c v Empty)

------------------------------------------------------------------------------
-- Examples and thoughts

-- Credit card example

cc : # NOT ⟷ # NOT
cc = Prim uniti⋆l ◎
     (((η+ NOT) ⊗ Prim id⟷) ◎
     ((Prim assocr⋆ ◎
     ((Prim id⟷ ⊗ Prim swap⋆) ◎
     ((Prim id⟷ ⊗ (ε+ NOT)) ◎
     Prim unite⋆r)))))

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

cnot : BOOL ⊗ BOOL ⟷ BOOL ⊗ BOOL
cnot = (foldSwap {𝟙} ⊗ Prim id⟷) ◎ ap⟷ ◎ (unfoldSwap ⊗ Prim id⟷)

-- (1+1) x b
-- dist 1xb + 1xb
-- 

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
------------------------------------------------------------------------------
