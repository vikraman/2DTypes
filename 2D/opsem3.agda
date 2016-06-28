{-# OPTIONS --without-K #-}

module 2D.opsem3 where

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
------------------------------------------------------------------------------
-- evaluation of simple combinators forwards and backwards

prim : {T₁ T₂ : U} → (Prim⟷ T₁ T₂) → Val T₁ → Val T₂
prim c v = {!!}

prim⁻¹ : {T₁ T₂ : U} → (Prim⟷ T₁ T₂) → Val T₂ → Val T₁
prim⁻¹ c v = {!!}

prim◎prim⁻¹≡id : {T₁ T₂ : U} → (c : Prim⟷ T₁ T₂) → (v : Val T₂) → prim c (prim⁻¹ c v) ≡ v
prim◎prim⁻¹≡id c v = {!!}

------------------------------------------------------------------------------
-- Evaluation

mutual
  {-# TERMINATING #-}
  𝓐𝓹 : {T₁ T₂ : U} → (T₁ ⟷ T₂) → Val T₁ → Val T₂
  𝓐𝓹 (Prim x) v = {!!}
  𝓐𝓹 (c ◎ c₁) v = {!!}
  𝓐𝓹 (c ⊕ c₁) v = {!!}
  𝓐𝓹 (c ⊗ c₁) v = {!!}
  𝓐𝓹 foldSwap v = {!!}
  𝓐𝓹 unfoldSwap v = {!!}
  𝓐𝓹 ap⟷ [ comb x , v₁ ] = [ (comb x) , (𝓐𝓹 (Iter.q x) v₁) ]
  𝓐𝓹 ap⁻¹⟷ v = {!!}
  𝓐𝓹 (η- c) (𝟙ₚ x) = [ (1/comb ⟪ c , id⇔ ⟫) , (comb x) ]
  𝓐𝓹 (η+ c) (𝟙ₚ x) = [ (comb x) , (1/comb ⟪ c , id⇔ ⟫) ]
  𝓐𝓹 (ε+ c) [ comb x , 1/comb x₁ ] = 𝟙ₚ x
  𝓐𝓹 (ε- c) [ 1/comb x , comb x₁ ] = 𝟙ₚ x₁
  𝓐𝓹 (unite⋆l# c) v = {!!}
  𝓐𝓹 (uniti⋆l# c) v = {!!}
  𝓐𝓹 (unite⋆r# c) v = {!!}
  𝓐𝓹 (uniti⋆r# c) v = {!!}
{-  prim c v
  𝓐𝓹 (p ◎ q) v = 𝓐𝓹 q (𝓐𝓹 p v)
  𝓐𝓹 (p ⊕ q) (inj₁ v , av) =
    case (𝓐𝓹 p (v , av)) of λ { (v' , av') → (inj₁ v') , av' }
  𝓐𝓹 (p ⊕ q) (inj₂ v , av) =
    case (𝓐𝓹 q (v , av)) of λ { (v' , av') → (inj₂ v') , av' }
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
  𝓐𝓹 ap⟷ ((perm iter q α , v) , (av₁ , av₂)) =
    case (𝓐𝓹 q (v , av₂)) of λ { (v' , av₂') → (perm iter q α , v') , (av₁ , av₂') } 
  𝓐𝓹 ap⁻¹⟷ ((perm iter p' p'⇔p^i , v) , (av₁ , av₂)) with (𝓐𝓹⁻¹ p' (v , av₂))
  ... | v' , av₂' = (perm iter p' p'⇔p^i , v') , (av₁ , av₂')
-}

  𝓐𝓹⁻¹ : {T₁ T₂ : U} → (T₁ ⟷ T₂) → Val T₂ → Val T₁
  𝓐𝓹⁻¹ (Prim x) v = {!!}
  𝓐𝓹⁻¹ (c ◎ c₁) v = {!!}
  𝓐𝓹⁻¹ (c ⊕ c₁) v = {!!}
  𝓐𝓹⁻¹ (c ⊗ c₁) v = {!!}
  𝓐𝓹⁻¹ foldSwap v = {!!}
  𝓐𝓹⁻¹ unfoldSwap v = {!!}
  𝓐𝓹⁻¹ ap⟷ [ comb x , v₁ ] = [ (comb x) , (𝓐𝓹⁻¹ (Iter.q x) v₁) ]
  𝓐𝓹⁻¹ ap⁻¹⟷ v = {!!}
  𝓐𝓹⁻¹ (η- c) [ v , comb x ] = 𝟙ₚ x
  𝓐𝓹⁻¹ (η+ c) v = {!!}
  𝓐𝓹⁻¹ (ε+ c) v = {!!}
  𝓐𝓹⁻¹ (ε- c) v = {!!}
  𝓐𝓹⁻¹ (unite⋆l# c) v = {!!}
  𝓐𝓹⁻¹ (uniti⋆l# c) v = {!!}
  𝓐𝓹⁻¹ (unite⋆r# c) v = {!!}
  𝓐𝓹⁻¹ (uniti⋆r# c) v = {!!}
  

fwd◎bwd≈id : {T₁ T₂ : U} → (c : T₁ ⟷ T₂) → (v : Val T₂) → (𝓐𝓹 c (𝓐𝓹⁻¹ c v)) ≈ v
fwd◎bwd≈id (Prim x) v = {!!}
fwd◎bwd≈id (c ◎ c₁) v = {!!}
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
fwd◎bwd≈id (η+ c) v = {!!}
fwd◎bwd≈id (ε+ c) v = {!!}
fwd◎bwd≈id (ε- c) v = {!!}
fwd◎bwd≈id (unite⋆l# c) v = {!!}
fwd◎bwd≈id (uniti⋆l# c) v = {!!}
fwd◎bwd≈id (unite⋆r# c) v = {!!}
fwd◎bwd≈id (uniti⋆r# c) v = {!!}


