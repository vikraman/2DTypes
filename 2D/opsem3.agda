{-# OPTIONS --without-K #-}

module 2D.opsem3 where

open import Level using () renaming (zero to l0; suc to lsuc)
open import Universe using (Universe)
open import Data.Empty
open import Data.Bool
open import Data.Sum hiding ([_,_])
open import Data.Product hiding (<_,_>;,_)

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
-- open import 2D.Frac
open import 2D.Order
-- open import 2D.Equality
open import 2D.Iter
open import 2D.Sing
open import 2D.ProgMorphisms
open import 2D.Power

data Val : (τ : U) → Set where
  ⋆ :       Val 𝟙
  inl :     {τ₁ τ₂ : U} → Val τ₁ → Val (τ₁ ⊕ τ₂)
  inr :     {τ₁ τ₂ : U} → Val τ₂ → Val (τ₁ ⊕ τ₂)
  [_,_] :   {τ₁ τ₂ : U} → Val τ₁ → Val τ₂ → Val (τ₁ ⊗ τ₂)
  comb :    {τ : U} {p : τ ⟷ τ} → Iter p →  Val (# p)
  1/comb :  {τ : U} {p : τ ⟷ τ} → Sing p → Val (1/# p)
  𝟙ₚ :       {τ : U} {p : τ ⟷ τ} → Iter p → Val (𝟙# p)

-- need two more cases for ⊕
data _≈_ : {t : U} → Val t → Val t → Set where
  ⋆≈  : ⋆ ≈ ⋆
  #p≈ : ∀ {t} {p : t ⟷ t} {p^i p^j : Iter p} (q : Sing p) → (r : Sing p) →
        Sing.p' q ◎ Iter.q p^i ⇔ Iter.q p^j ◎ Sing.p' r → (comb p^i) ≈ (comb p^j)
  1/#p≈ : ∀ {t} {p : t ⟷ t} {p₁ p₂ : Sing p} (q : Iter p) → (r : Iter p) →
        Iter.q q ◎ Sing.p' p₁ ⇔ Sing.p' p₂ ◎ Iter.q r → (1/comb p₁) ≈ (1/comb p₂)
  𝟙ₚ≈ : ∀ {t} {p : t ⟷ t} → {p₁ p₂ : Iter p} (q : Iter p) → (r : Iter p) →
        Iter.q q ◎ Iter.q p₁ ⇔ Iter.q p₂ ◎ Iter.q r → (𝟙ₚ q) ≈ (𝟙ₚ r)
  [,]≈ : {s t : U} {sv₁ sv₂ : Val s} {tv₁ tv₂ : Val t} → sv₁ ≈ sv₂ → tv₁ ≈ tv₂ → [ sv₁ , tv₁ ] ≈ [ sv₂ , tv₂ ]
  -- this is rather useful in multiple instances
  refl≈ : ∀ {t} {v w : Val t} → v ≡ w → v ≈ w
  
------------------------------------------------------------------------------
-- evaluation of simple combinators forwards and backwards

-- should probably move all of this to 2D.Prim
prim : {T₁ T₂ : U} → (Prim⟷ T₁ T₂) → Val T₁ → Val T₂
prim unite₊l (inl ())
prim unite₊l (inr v) = v
prim uniti₊l v = inr v
prim unite₊r (inl v) = v
prim unite₊r (inr ())
prim uniti₊r v = inl v
prim swap₊ (inl v) = inr v
prim swap₊ (inr v) = inl v
prim assocl₊ (inl v) = inl (inl v)
prim assocl₊ (inr (inl v)) = inl (inr v)
prim assocl₊ (inr (inr v)) = inr v
prim assocr₊ (inl (inl v)) = inl v
prim assocr₊ (inl (inr v)) = inr (inl v)
prim assocr₊ (inr v) = inr (inr v)
prim unite⋆l [ v , w ] = w
prim uniti⋆l v = [ ⋆ , v ]
prim unite⋆r [ v , v₁ ] = v
prim uniti⋆r v = [ v , ⋆ ]
prim swap⋆ [ v , w ] = [ w , v ]
prim assocl⋆ [ v , [ w , z ] ] = [ [ v , w ] , z ]
prim assocr⋆ [ [ v , w ] , z ] = [ v , [ w , z ] ]
prim absorbr [ v , v₁ ] = v -- note how we pass v through, even though it's 𝟘
prim absorbl [ v , v₁ ] = v₁
prim factorzr () -- but here we can't invent values, so we have no choice
prim factorzl ()
prim dist [ inl v , w ] = inl [ v , w ]
prim dist [ inr v , w ] = inr [ v , w ]
prim factor (inl [ v , v₁ ]) = [ inl v , v₁ ]
prim factor (inr [ v , v₁ ]) = [ inr v , v₁ ]
prim distl [ v , inl v₁ ] = inl [ v , v₁ ]
prim distl [ v , inr v₁ ] = inr [ v , v₁ ]
prim factorl (inl [ v , v₁ ]) = [ v , inl v₁ ]
prim factorl (inr [ v , v₁ ]) = [ v , inr v₁ ]
prim id⟷ v = v

prim⁻¹ : {T₁ T₂ : U} → (Prim⟷ T₁ T₂) → Val T₂ → Val T₁
prim⁻¹ unite₊l v = inr v
prim⁻¹ uniti₊l (inl ())
prim⁻¹ uniti₊l (inr v) = v
prim⁻¹ unite₊r v = inl v
prim⁻¹ uniti₊r (inl v) = v
prim⁻¹ uniti₊r (inr ())
prim⁻¹ swap₊ (inl v) = inr v
prim⁻¹ swap₊ (inr v) = inl v
prim⁻¹ assocl₊ (inl (inl v)) = inl v
prim⁻¹ assocl₊ (inl (inr v)) = inr (inl v)
prim⁻¹ assocl₊ (inr v) = inr (inr v)
prim⁻¹ assocr₊ (inl v) = inl (inl v)
prim⁻¹ assocr₊ (inr (inl v)) = inl (inr v)
prim⁻¹ assocr₊ (inr (inr v)) = inr v
prim⁻¹ unite⋆l v = [ ⋆ , v ]
prim⁻¹ uniti⋆l [ v , v₁ ] = v₁
prim⁻¹ unite⋆r v = [ v , ⋆ ]
prim⁻¹ uniti⋆r [ v , v₁ ] = v
prim⁻¹ swap⋆ [ v , v₁ ] = [ v₁ , v ]
prim⁻¹ assocl⋆ [ [ v , v₁ ] , v₂ ] = [ v , [ v₁ , v₂ ] ]
prim⁻¹ assocr⋆ [ v , [ v₁ , v₂ ] ] = [ [ v , v₁ ] , v₂ ]
prim⁻¹ absorbr ()
prim⁻¹ absorbl ()
prim⁻¹ factorzr [ v , v₁ ] = v₁
prim⁻¹ factorzl [ v , v₁ ] = v
prim⁻¹ dist (inl [ v , v₁ ]) = [ inl v , v₁ ]
prim⁻¹ dist (inr [ v , v₁ ]) = [ inr v , v₁ ]
prim⁻¹ factor [ inl v , v₁ ] = inl [ v , v₁ ]
prim⁻¹ factor [ inr v , v₁ ] = inr [ v , v₁ ]
prim⁻¹ distl (inl [ v , v₁ ]) = [ v , inl v₁ ]
prim⁻¹ distl (inr [ v , v₁ ]) = [ v , inr v₁ ]
prim⁻¹ factorl [ v , inl v₁ ] = inl [ v , v₁ ]
prim⁻¹ factorl [ v , inr v₁ ] = inr [ v , v₁ ]
prim⁻¹ id⟷ v = v

prim◎prim⁻¹≡id : {T₁ T₂ : U} → (c : Prim⟷ T₁ T₂) → (v : Val T₂) → prim c (prim⁻¹ c v) ≡ v
prim◎prim⁻¹≡id unite₊l v = refl
prim◎prim⁻¹≡id uniti₊l (inl ())
prim◎prim⁻¹≡id uniti₊l (inr v) = refl
prim◎prim⁻¹≡id unite₊r v = refl
prim◎prim⁻¹≡id uniti₊r (inl v) = refl
prim◎prim⁻¹≡id uniti₊r (inr ())
prim◎prim⁻¹≡id swap₊ (inl v) = refl
prim◎prim⁻¹≡id swap₊ (inr v) = refl
prim◎prim⁻¹≡id assocl₊ (inl (inl v)) = refl
prim◎prim⁻¹≡id assocl₊ (inl (inr v)) = refl
prim◎prim⁻¹≡id assocl₊ (inr v) = refl
prim◎prim⁻¹≡id assocr₊ (inl v) = refl
prim◎prim⁻¹≡id assocr₊ (inr (inl v)) = refl
prim◎prim⁻¹≡id assocr₊ (inr (inr v)) = refl
prim◎prim⁻¹≡id unite⋆l v = refl
prim◎prim⁻¹≡id uniti⋆l [ ⋆ , v₁ ] = refl
prim◎prim⁻¹≡id unite⋆r v = refl
prim◎prim⁻¹≡id uniti⋆r [ v , ⋆ ] = refl
prim◎prim⁻¹≡id swap⋆ [ v , v₁ ] = refl
prim◎prim⁻¹≡id assocl⋆ [ [ v , v₁ ] , v₂ ] = refl
prim◎prim⁻¹≡id assocr⋆ [ v , [ v₁ , v₂ ] ] = refl
prim◎prim⁻¹≡id absorbl ()
prim◎prim⁻¹≡id absorbr ()
prim◎prim⁻¹≡id factorzr [ v , () ]
prim◎prim⁻¹≡id factorzl [ () , v₁ ]
prim◎prim⁻¹≡id dist (inl [ v , v₁ ]) = refl
prim◎prim⁻¹≡id dist (inr [ v , v₁ ]) = refl
prim◎prim⁻¹≡id factor [ inl v , v₁ ] = refl
prim◎prim⁻¹≡id factor [ inr v , v₁ ] = refl
prim◎prim⁻¹≡id distl (inl [ v , v₁ ]) = refl
prim◎prim⁻¹≡id distl (inr [ v , v₁ ]) = refl
prim◎prim⁻¹≡id factorl [ v , inl v₁ ] = refl
prim◎prim⁻¹≡id factorl [ v , inr v₁ ] = refl
prim◎prim⁻¹≡id id⟷ v = refl

------------------------------------------------------------------------------
-- Evaluation

mutual
  {-# TERMINATING #-}
  𝓐𝓹 : {T₁ T₂ : U} → (T₁ ⟷ T₂) → Val T₁ → Val T₂
  𝓐𝓹 (Prim x) v = prim x v
  𝓐𝓹 (c ◎ c₁) v = 𝓐𝓹 c₁ (𝓐𝓹 c v)
  𝓐𝓹 (c ⊕ c₁) (inl v) = inl (𝓐𝓹 c v)
  𝓐𝓹 (c ⊕ c₁) (inr v) = inr (𝓐𝓹 c₁ v)
  𝓐𝓹 (c ⊗ c₁) [ v , w ] = [ 𝓐𝓹 c v , 𝓐𝓹 c₁ w ]
  𝓐𝓹 foldSwap v = {!!}
  𝓐𝓹 unfoldSwap v = {!!}
  𝓐𝓹 ap⟷ [ comb x , v₁ ] = [ (comb x) , (𝓐𝓹 (Iter.q x) v₁) ]
  𝓐𝓹 ap⁻¹⟷ [ comb x , v₁ ] = [ (comb x) , (𝓐𝓹⁻¹ (Iter.q x) v₁) ]
  𝓐𝓹 (η- c) (𝟙ₚ x) = [ (1/comb ⟪ c , id⇔ ⟫) , (comb x) ]
  𝓐𝓹 (η+ c) (𝟙ₚ x) = [ (comb x) , (1/comb ⟪ c , id⇔ ⟫) ]
  𝓐𝓹 (ε+ c) [ comb x , 1/comb x₁ ] = 𝟙ₚ x
  𝓐𝓹 (ε- c) [ 1/comb x , comb x₁ ] = 𝟙ₚ x₁
  𝓐𝓹 (unite⋆l# c) [ v , v₁ ] = v₁
  𝓐𝓹 (uniti⋆l# c) v = [ (𝟙ₚ ( < (+ 1) , c , idr◎r > )) , v ]
  𝓐𝓹 (unite⋆r# c) [ v , v₁ ] = v
  𝓐𝓹 (uniti⋆r# c) v = [ v , (𝟙ₚ < + 1 , c , idr◎r >) ]

  𝓐𝓹⁻¹ : {T₁ T₂ : U} → (T₁ ⟷ T₂) → Val T₂ → Val T₁
  𝓐𝓹⁻¹ (Prim x) v = prim⁻¹ x v
  𝓐𝓹⁻¹ (c ◎ c₁) v = 𝓐𝓹⁻¹ c (𝓐𝓹⁻¹ c₁ v)
  𝓐𝓹⁻¹ (c ⊕ c₁) v = {!!}
  𝓐𝓹⁻¹ (c ⊗ c₁) v = {!!}
  𝓐𝓹⁻¹ foldSwap v = {!!}
  𝓐𝓹⁻¹ unfoldSwap v = {!!}
  𝓐𝓹⁻¹ ap⟷ [ comb x , v₁ ] = [ (comb x) , (𝓐𝓹⁻¹ (Iter.q x) v₁) ]
  𝓐𝓹⁻¹ ap⁻¹⟷ v = {!!}
  𝓐𝓹⁻¹ (η- c) [ v , comb x ] = 𝟙ₚ x
  𝓐𝓹⁻¹ (η+ c) [ comb x , v₁ ] = 𝟙ₚ x
  𝓐𝓹⁻¹ (ε+ c) (𝟙ₚ x) = [ (comb x) , (1/comb ⟪ c , id⇔ ⟫) ]
  𝓐𝓹⁻¹ (ε- c) (𝟙ₚ x) = [ (1/comb ⟪ c , id⇔ ⟫) , (comb x) ]
  𝓐𝓹⁻¹ (unite⋆l# c) v = {!!}
  𝓐𝓹⁻¹ (uniti⋆l# c) v = {!!}
  𝓐𝓹⁻¹ (unite⋆r# c) v = {!!}
  𝓐𝓹⁻¹ (uniti⋆r# c) v = {!!}
  

fwd◎bwd≈id : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → (v : Val T₂) → (𝓐𝓹 c (𝓐𝓹⁻¹ c v)) ≈ v
fwd◎bwd≈id (Prim x) v = refl≈ (prim◎prim⁻¹≡id x v)
fwd◎bwd≈id (c ◎ c₁) v = {!!} -- is going to need cong≈
fwd◎bwd≈id (c ⊕ c₁) v = {!!}
fwd◎bwd≈id (c ⊗ c₁) v = {!!}
fwd◎bwd≈id foldSwap v = {!!}
fwd◎bwd≈id unfoldSwap v = {!!}
fwd◎bwd≈id ap⟷ [ comb {t} {p} < i , q , α > , v₁ ] =
  [,]≈ (#p≈ ⟪ p , id⇔ ⟫ ⟪ p , id⇔ ⟫ (id⇔ ⊡ α ● assoc1g i ● (2! α) ⊡ id⇔))
  (fwd◎bwd≈id q v₁)
fwd◎bwd≈id ap⁻¹⟷ v = {!!}
fwd◎bwd≈id (η- c) [ 1/comb x , comb x₁ ] =
  [,]≈ (1/#p≈ x₁ x₁ (id⇔ ⊡ 2! (Sing.eq x) ● 2! (swapSI x x₁)))
       (#p≈ x x (swapSI x x₁))
fwd◎bwd≈id (η+ c) [ comb x , 1/comb x₁ ] =
  [,]≈ (#p≈ x₁ x₁ (swapSI x₁ x))
       (1/#p≈ x x (id⇔ ⊡ 2! (Sing.eq x₁) ● 2! (swapSI x₁ x)))
fwd◎bwd≈id (ε+ c) (𝟙ₚ x) = 𝟙ₚ≈ {p₁ = x} {x} x x id⇔ -- trivial?  See below!
  -- note that this means that we get x back on the nose.
fwd◎bwd≈id (ε- c) (𝟙ₚ x) = refl≈ refl -- 𝟙ₚ≈ {p₁ = x} {x} x x id⇔
fwd◎bwd≈id (unite⋆l# c) v = {!!}
fwd◎bwd≈id (uniti⋆l# c) v = {!!}
fwd◎bwd≈id (unite⋆r# c) v = {!!}
fwd◎bwd≈id (uniti⋆r# c) v = {!!}


