{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import HoTT

open import Pi+.Coxeter.Sn hiding (Sn)
open import Pi+.Coxeter.Group
open import Pi+.Coxeter.Coxeter
open import Pi+.Extra
open import Pi+.Misc

module Pi+.Coxeter.GeneratedGroupIso (n : ℕ) where

  open import Pi+.Coxeter.GeneratedGroup n

  ηᴳ♯-β : ∀ w → GroupHom.f ηᴳ♯ q[ w ] == q[ map codiag w ]
  ηᴳ♯-β w = Word-extendᴳ-η w ∙ ap q[_] (Word-extendˢ-η w)

  η-εˢ : ∀ l → GroupHom.f ηᴳ♯ (εᴳ l) == q[ l ]
  η-εˢ l = ηᴳ♯-β (map inl l) ∙ ap q[_] (map-∘ inl codiag ∙ map-id)

  η-εᴳ : ∀ g → GroupHom.f ηᴳ♯ (GroupHom.f ε g) == g
  η-εᴳ = SetQuot-elim η-εˢ (λ r → prop-has-all-paths-↓)

  GRel-refl : ∀ w → w ≈ᴳ w
  GRel-refl w = idp {n}

  ε-ηˢ-w : ∀ w → map inl (map codiag w) ≈ᴳ w
  ε-ηˢ-w nil = GRel-refl nil
  ε-ηˢ-w (x :: w) =
    ::-respects-≈ {x = codiag x} (transport (_≈* (map codiag w)) (! (map-∘ inl codiag ∙ map-id)) (GRel-refl w))

  ε-ηˢ : ∀ w → SetQuot-rec εᴳ εᴳ-respects-≈ (GroupHom.f ηᴳ♯ q[ w ]) == q[ w ]
  ε-ηˢ w = ap (SetQuot-rec εᴳ εᴳ-respects-≈) (ηᴳ♯-β w) ∙ quot-rel (GG.qwr-rel (ε-ηˢ-w w))

  ε-ηᴳ : ∀ w → GroupHom.f ε (GroupHom.f ηᴳ♯ w) == w
  ε-ηᴳ = SetQuot-elim ε-ηˢ (λ r → prop-has-all-paths-↓)
