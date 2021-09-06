{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import HoTT

open import Pi.Extra
open import Pi.Misc

module Pi.Coxeter.GeneratedGroupIsoGeneralised
  {i j} (A : Type i) {{_ : is-set A}}
  (_≈_ : List A → List A → Type j)
  (≈-refl : is-refl _≈_)
  (≈-cong-reverse : ∀ {a₁ a₂} → a₁ ≈ a₂ → reverse a₁ ≈ reverse a₂)
  (≈-cong-++ : ∀ {a₁ a₂ b₁ b₂} → a₁ ≈ a₂ → b₁ ≈ b₂ → (a₁ ++ b₁) ≈ (a₂ ++ b₂))
  (≈-inv-l : ∀ l → (reverse l ++ l) ≈ nil)
  where

  ≈-cong-:: : ∀ {x w₁ w₂} → w₁ ≈ w₂ → (x :: w₁) ≈ (x :: w₂)
  ≈-cong-:: {x = x} r = ≈-cong-++ (≈-refl (x :: nil)) r

  open import Pi.Coxeter.GeneratedGroupGeneralised A _≈_ ≈-refl ≈-cong-reverse ≈-cong-++ ≈-inv-l

  ηᴳ♯-β : ∀ w → GroupHom.f ηᴳ♯ q[ w ] == q[ map codiag w ]
  ηᴳ♯-β w = Word-extendᴳ-η w ∙ ap q[_] (Word-extendˢ-η w)

  η-εˢ : ∀ l → GroupHom.f ηᴳ♯ (εᴳ l) == q[ l ]
  η-εˢ l = ηᴳ♯-β (map inl l) ∙ ap q[_] (map-∘ inl codiag ∙ map-id)

  η-εᴳ : ∀ g → GroupHom.f ηᴳ♯ (GroupHom.f ε g) == g
  η-εᴳ = SetQuot-elim η-εˢ (λ r → prop-has-all-paths-↓)

  GRel-refl : ∀ w → w ≈ᴳ w
  GRel-refl w = ≈-refl (map codiag w)

  ε-ηˢ-w : ∀ w → map inl (map codiag w) ≈ᴳ w
  ε-ηˢ-w nil = GRel-refl nil
  ε-ηˢ-w (x :: w) =
    ≈-cong-:: {x = codiag x} (transport (λ l → _≈_ l (map codiag w)) (! (map-∘ inl codiag ∙ map-id)) (GRel-refl w))

  ε-ηˢ : ∀ w → SetQuot-rec εᴳ εᴳ-respects-≈ (GroupHom.f ηᴳ♯ q[ w ]) == q[ w ]
  ε-ηˢ w = ap (SetQuot-rec εᴳ εᴳ-respects-≈) (ηᴳ♯-β w) ∙ quot-rel (GG.qwr-rel (ε-ηˢ-w w))

  ε-ηᴳ : ∀ w → GroupHom.f ε (GroupHom.f ηᴳ♯ w) == w
  ε-ηᴳ = SetQuot-elim ε-ηˢ (λ r → prop-has-all-paths-↓)
