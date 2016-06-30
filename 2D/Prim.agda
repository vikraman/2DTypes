{-# OPTIONS --without-K #-}

module 2D.Prim where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import 2D.Types
open import 2D.Val

------------------------------------------------------------------------------
-- evaluation of simple combinators forwards and backwards

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

