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

prim⁻¹◎prim≡id : {T₁ T₂ : U} → (c : Prim⟷ T₁ T₂) → (v : Val T₁) → prim⁻¹ c (prim c v) ≡ v
prim⁻¹◎prim≡id unite₊l (inl ())
prim⁻¹◎prim≡id unite₊l (inr v) = refl
prim⁻¹◎prim≡id uniti₊l v = refl
prim⁻¹◎prim≡id unite₊r (inl v) = refl
prim⁻¹◎prim≡id unite₊r (inr ())
prim⁻¹◎prim≡id uniti₊r v = refl
prim⁻¹◎prim≡id swap₊ (inl v) = refl
prim⁻¹◎prim≡id swap₊ (inr v) = refl
prim⁻¹◎prim≡id assocl₊ (inl v) = refl
prim⁻¹◎prim≡id assocl₊ (inr (inl v)) = refl
prim⁻¹◎prim≡id assocl₊ (inr (inr v)) = refl
prim⁻¹◎prim≡id assocr₊ (inl (inl v)) = refl
prim⁻¹◎prim≡id assocr₊ (inl (inr v)) = refl
prim⁻¹◎prim≡id assocr₊ (inr v) = refl
prim⁻¹◎prim≡id unite⋆l [ ⋆ , v₁ ] = refl
prim⁻¹◎prim≡id uniti⋆l v = refl
prim⁻¹◎prim≡id unite⋆r [ v , ⋆ ] = refl
prim⁻¹◎prim≡id uniti⋆r v = refl
prim⁻¹◎prim≡id swap⋆ [ v , v₁ ] = refl
prim⁻¹◎prim≡id assocl⋆ [ v , [ v₁ , v₂ ] ] = refl
prim⁻¹◎prim≡id assocr⋆ [ [ v , v₁ ] , v₂ ] = refl
prim⁻¹◎prim≡id absorbr [ () , v₁ ]
prim⁻¹◎prim≡id absorbl [ v , () ]
prim⁻¹◎prim≡id factorzr ()
prim⁻¹◎prim≡id factorzl ()
prim⁻¹◎prim≡id dist [ inl v , v₁ ] = refl
prim⁻¹◎prim≡id dist [ inr v , v₁ ] = refl
prim⁻¹◎prim≡id factor (inl [ v , v₁ ]) = refl
prim⁻¹◎prim≡id factor (inr [ v , v₁ ]) = refl
prim⁻¹◎prim≡id distl [ v , inl v₁ ] = refl
prim⁻¹◎prim≡id distl [ v , inr v₁ ] = refl
prim⁻¹◎prim≡id factorl (inl [ v , v₁ ]) = refl
prim⁻¹◎prim≡id factorl (inr [ v , v₁ ]) = refl
prim⁻¹◎prim≡id id⟷ v = refl

prim-cong≈ : {T₁ T₂ : U} → (c : Prim⟷ T₁ T₂) → (v w : Val T₁) → v ≈ w → prim c v ≈ prim c w
prim-cong≈ unite₊l (inl ()) w eq
prim-cong≈ unite₊l (inr v) (inl ()) eq
prim-cong≈ unite₊l (inr v) (inr w) (inj≈ x) = x
prim-cong≈ uniti₊l v w eq = inj≈ eq
prim-cong≈ unite₊r (inl v) (inl w) (inj≈ x) = x
prim-cong≈ unite₊r (inl v) (inr ()) eq
prim-cong≈ unite₊r (inr ()) w eq
prim-cong≈ uniti₊r v w eq = inj≈ eq
prim-cong≈ swap₊ (inl v) (inl w) (inj≈ x) = inj≈ x
prim-cong≈ swap₊ (inl v) (inr w) (inj≈ ())
prim-cong≈ swap₊ (inr v) (inl w) (inj≈ ())
prim-cong≈ swap₊ (inr v) (inr w) (inj≈ x) = inj≈ x
prim-cong≈ assocl₊ (inl v) (inl w) (inj≈ x) = inj≈ (inj≈ x)
prim-cong≈ assocl₊ (inl v) (inr (inl w)) (inj≈ ())
prim-cong≈ assocl₊ (inl v) (inr (inr w)) (inj≈ ())
prim-cong≈ assocl₊ (inr v) (inl w) (inj≈ ())
prim-cong≈ assocl₊ (inr (inl v)) (inr (inl w)) (inj≈ (inj≈ x)) = inj≈ (inj≈ x)
prim-cong≈ assocl₊ (inr (inr v)) (inr (inl w)) (inj≈ (inj≈ x)) = inj≈ x
prim-cong≈ assocl₊ (inr (inl v)) (inr (inr w)) (inj≈ (inj≈ ()))
prim-cong≈ assocl₊ (inr (inr v)) (inr (inr w)) (inj≈ (inj≈ x)) = inj≈ x
prim-cong≈ assocr₊ (inl (inl v)) (inl (inl w)) (inj≈ (inj≈ x)) = inj≈ x
prim-cong≈ assocr₊ (inl (inl v)) (inl (inr w)) (inj≈ (inj≈ ()))
prim-cong≈ assocr₊ (inl (inr v)) (inl (inl w)) (inj≈ (inj≈ ()))
prim-cong≈ assocr₊ (inl (inr v)) (inl (inr w)) (inj≈ (inj≈ x)) = inj≈ (inj≈ x)
prim-cong≈ assocr₊ (inl (inl v)) (inr w) (inj≈ ())
prim-cong≈ assocr₊ (inl (inr v)) (inr w) (inj≈ ())
prim-cong≈ assocr₊ (inr v) (inl (inl w)) (inj≈ ())
prim-cong≈ assocr₊ (inr v) (inl (inr w)) (inj≈ ())
prim-cong≈ assocr₊ (inr v) (inr w) (inj≈ x) = inj≈ (inj≈ x)
prim-cong≈ unite⋆l [ v , v₁ ] [ w , w₁ ] ([,]≈ eq eq₁) = eq₁
prim-cong≈ uniti⋆l v w eq = [,]≈ ⋆≈ eq
prim-cong≈ unite⋆r [ v , v₁ ] [ w , w₁ ] ([,]≈ eq eq₁) = eq
prim-cong≈ uniti⋆r v w eq = [,]≈ eq ⋆≈
prim-cong≈ swap⋆ [ v , v₁ ] [ w , w₁ ] ([,]≈ eq eq₁) = [,]≈ eq₁ eq
prim-cong≈ assocl⋆ [ v , [ v₁ , v₂ ] ] [ w , [ w₁ , w₂ ] ] ([,]≈ eq ([,]≈ eq₁ eq₂)) = [,]≈ ([,]≈ eq eq₁) eq₂
prim-cong≈ assocr⋆ [ [ v , v₁ ] , v₂ ] [ [ w , w₁ ] , w₂ ] ([,]≈ ([,]≈ eq eq₁) eq₂) = [,]≈ eq ([,]≈ eq₁ eq₂)
prim-cong≈ absorbr [ () , v₁ ] w eq
prim-cong≈ absorbl [ v , () ] w eq
prim-cong≈ factorzr () w eq
prim-cong≈ factorzl () w eq
prim-cong≈ dist [ inl v , v₁ ] [ inl w , w₁ ] ([,]≈ (inj≈ x) eq₁) = inj≈ ([,]≈ x eq₁)
prim-cong≈ dist [ inl v , v₁ ] [ inr w , w₁ ] ([,]≈ (inj≈ x) eq₁) = inj≈ x
prim-cong≈ dist [ inr v , v₁ ] [ inl w , w₁ ] ([,]≈ (inj≈ x) eq₁) = inj≈ x
prim-cong≈ dist [ inr v , v₁ ] [ inr w , w₁ ] ([,]≈ (inj≈ x) eq₁) = inj≈ ([,]≈ x eq₁)
prim-cong≈ factor (inl [ v , v₁ ]) (inl [ w , w₁ ]) (inj≈ ([,]≈ x x₁)) = [,]≈ (inj≈ x) x₁
prim-cong≈ factor (inl [ v , v₁ ]) (inr [ w , w₁ ]) (inj≈ ())
prim-cong≈ factor (inr [ v , v₁ ]) (inl [ w , w₁ ]) (inj≈ ())
prim-cong≈ factor (inr [ v , v₁ ]) (inr [ w , w₁ ]) (inj≈ ([,]≈ x x₁)) = [,]≈ (inj≈ x) x₁
prim-cong≈ distl [ v , inl v₁ ] [ w , inl w₁ ] ([,]≈ eq (inj≈ x)) = inj≈ ([,]≈ eq x)
prim-cong≈ distl [ v , inl v₁ ] [ w , inr w₁ ] ([,]≈ eq (inj≈ ()))
prim-cong≈ distl [ v , inr v₁ ] [ w , inl w₁ ] ([,]≈ eq (inj≈ ()))
prim-cong≈ distl [ v , inr v₁ ] [ w , inr w₁ ] ([,]≈ eq (inj≈ x)) = inj≈ ([,]≈ eq x)
prim-cong≈ factorl (inl [ v , v₁ ]) (inl [ w , w₁ ]) (inj≈ ([,]≈ x x₁)) = [,]≈ x (inj≈ x₁)
prim-cong≈ factorl (inl [ v , v₁ ]) (inr [ w , w₁ ]) (inj≈ ())
prim-cong≈ factorl (inr [ v , v₁ ]) (inl [ w , w₁ ]) (inj≈ ())
prim-cong≈ factorl (inr [ v , v₁ ]) (inr [ w , w₁ ]) (inj≈ ([,]≈ x x₁)) = [,]≈ x (inj≈ x₁)
prim-cong≈ id⟷ v w eq = eq

postulate
  prim⁻¹-cong≈ : {T₁ T₂ : U} → (c : Prim⟷ T₁ T₂) → (v w : Val T₂) → v ≈ w → prim⁻¹ c v ≈ prim⁻¹ c w

{-
prim⁻¹-cong≈ : {T₁ T₂ : U} → (c : Prim⟷ T₁ T₂) → (v w : Val T₂) → v ≈ w → prim⁻¹ c v ≈ prim⁻¹ c w
prim⁻¹-cong≈ unite₊l v w eq = {!!}
prim⁻¹-cong≈ uniti₊l v w eq = {!!}
prim⁻¹-cong≈ unite₊r v w eq = {!!}
prim⁻¹-cong≈ uniti₊r v w eq = {!!}
prim⁻¹-cong≈ swap₊ v w eq = {!!}
prim⁻¹-cong≈ assocl₊ v w eq = {!!}
prim⁻¹-cong≈ assocr₊ v w eq = {!!}
prim⁻¹-cong≈ unite⋆l v w eq = {!!}
prim⁻¹-cong≈ uniti⋆l v w eq = {!!}
prim⁻¹-cong≈ unite⋆r v w eq = {!!}
prim⁻¹-cong≈ uniti⋆r v w eq = {!!}
prim⁻¹-cong≈ swap⋆ v w eq = {!!}
prim⁻¹-cong≈ assocl⋆ v w eq = {!!}
prim⁻¹-cong≈ assocr⋆ v w eq = {!!}
prim⁻¹-cong≈ absorbr v w eq = {!!}
prim⁻¹-cong≈ absorbl v w eq = {!!}
prim⁻¹-cong≈ factorzr v w eq = {!!}
prim⁻¹-cong≈ factorzl v w eq = {!!}
prim⁻¹-cong≈ dist v w eq = {!!}
prim⁻¹-cong≈ factor v w eq = {!!}
prim⁻¹-cong≈ distl v w eq = {!!}
prim⁻¹-cong≈ factorl v w eq = {!!}
prim⁻¹-cong≈ id⟷ v w eq = eq
-}
