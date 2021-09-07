{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import HoTT

open import Pi.Common.Extra
open import Pi.Common.Misc

-- If we have a group structure S on (List A, R)
-- then we can lift it uniquely to (List (PlusMinus A), R')

module Pi.Coxeter.GeneratedGroupGeneralised
  {i j} (A : Type i) {{_ : is-set A}}
  (_≈_ : List A → List A → Type j)
  (≈-refl : is-refl _≈_)
  (≈-cong-reverse : ∀ {a₁ a₂} → a₁ ≈ a₂ → reverse a₁ ≈ reverse a₂)
  (≈-cong-++ : ∀ {a₁ a₂ b₁ b₂} → a₁ ≈ a₂ → b₁ ≈ b₂ → (a₁ ++ b₁) ≈ (a₂ ++ b₂))
  (≈-inv-l : ∀ l → (reverse l ++ l) ≈ nil)
  where

  GRel : Rel (Word A) j
  GRel w1 w2 = map codiag w1 ≈ map codiag w2

  syntax GRel w1 w2 = w1 ≈ᴳ w2

  module GG = GeneratedGroup A GRel
  G = GG.GenGroup

  GS : GroupStructure (SetQuot _≈_)
  GroupStructure.ident GS =
    q[ nil ]
  GroupStructure.inv GS =
    SetQuot-map reverse ≈-cong-reverse
  GroupStructure.comp GS =
    SetQuot-map2 _++_ ≈-refl ≈-cong-++
  GroupStructure.unit-l GS =
    SetQuot-elim (λ l → idp) (λ p → prop-has-all-paths-↓)
  GroupStructure.assoc GS =
    SetQuot-elim (λ l1 → SetQuot-elim (λ l2 → SetQuot-elim (λ l3 →
      ap q[_] (++-assoc l1 l2 l3))
        (λ r → prop-has-all-paths-↓))
          (λ r → prop-has-all-paths-↓))
            (λ r → prop-has-all-paths-↓)
  GroupStructure.inv-l GS =
    SetQuot-elim (quot-rel ∘ ≈-inv-l) (λ r → prop-has-all-paths-↓)

  SG : Group (lmax i j)
  Group.El SG = SetQuot _≈_
  Group.El-level SG = ⟨⟩
  Group.group-struct SG = GS

  open GG.HomomorphismEquiv SG

  ηˢ : A → List A
  ηˢ = _:: nil

  ηᴳ : A → Group.El SG
  ηᴳ = q[_] ∘ ηˢ

  PlusMinus-extendˢ : PlusMinus A → List A
  PlusMinus-extendˢ (inl a) = ηˢ a
  PlusMinus-extendˢ (inr a) = reverse (ηˢ a)

  PlusMinus-extendᴳ-η : ∀ w → PlusMinus-extendᴳ SG ηᴳ w == q[ PlusMinus-extendˢ w ]
  PlusMinus-extendᴳ-η (inl a) = idp
  PlusMinus-extendᴳ-η (inr a) = idp

  Word-extendˢ : Word A → List A
  Word-extendˢ = foldr' _++_ nil ∘ map PlusMinus-extendˢ

  Word-extendˢ-η : ∀ w → Word-extendˢ w == map codiag w
  Word-extendˢ-η nil = idp
  Word-extendˢ-η (inl x :: nil) = idp
  Word-extendˢ-η (inr x :: nil) = idp
  Word-extendˢ-η (inl x :: w@(_ :: _)) = ap (x ::_) (Word-extendˢ-η w)
  Word-extendˢ-η (inr x :: w@(_ :: _)) = ap (x ::_) (Word-extendˢ-η w)

  Word-extendᴳ-η : ∀ w → Word-extendᴳ SG ηᴳ w == q[ Word-extendˢ w ]
  Word-extendᴳ-η nil = idp
  Word-extendᴳ-η (x :: nil) =
      Word-extendᴳ-:: SG ηᴳ x nil
    ∙ ap (λ l → Group.comp SG l q[ nil ]) (PlusMinus-extendᴳ-η x)
    ∙ ap q[_] (++-unit-r (PlusMinus-extendˢ x))
  Word-extendᴳ-η (x :: w@(_ :: _)) =
      Word-extendᴳ-:: SG ηᴳ x w
    ∙ ap2 (Group.comp SG) (PlusMinus-extendᴳ-η x) (Word-extendᴳ-η w)

  η-respects-relˢ : ∀ {w1 w2} → GRel w1 w2 → Word-extendˢ w1 ≈ Word-extendˢ w2
  η-respects-relˢ {w1} {w2} r = transport2 _≈_ (! (Word-extendˢ-η w1)) (! (Word-extendˢ-η w2)) r

  abstract
    η-respects-relᴳ : respects-rel ηᴳ
    η-respects-relᴳ {w1} {w2} r = Word-extendᴳ-η w1 ∙ quot-rel (η-respects-relˢ r) ∙ ! (Word-extendᴳ-η w2)

  module R = RelationRespectingFunctions A GRel SG
  open R.RelationRespectingFunction

  ηᴳ♯ : G →ᴳ SG
  ηᴳ♯ = GG.HomomorphismEquiv.extend SG (rel-res-fun ηᴳ η-respects-relᴳ)

  εᴳ : List A → Group.El G
  εᴳ = q[_] ∘ map inl

  map-inl-respects-≈ : {w1 w2 : List A} → w1 ≈ w2 → map inl w1 ≈ᴳ map inl w2
  map-inl-respects-≈ {nil} {nil} r =
    ≈-refl nil
  map-inl-respects-≈ {nil} {x :: w2} r =
    transport (_≈_ nil) (ap (x ::_) (! (map-∘ inl codiag ∙ map-id))) r
  map-inl-respects-≈ {x :: w1} {nil} r =
    transport (λ l → _≈_ l nil) (ap (x ::_) (! (map-∘ inl codiag ∙ map-id))) r
  map-inl-respects-≈ {x :: w1} {y :: w2} r =
    transport2 _≈_ (ap (x ::_) (! (map-∘ inl codiag ∙ map-id))) (ap (y ::_) (! (map-∘ inl codiag ∙ map-id))) r

  abstract
    εᴳ-respects-≈ : {w1 w2 : List A} → w1 ≈ w2 → εᴳ w1 == εᴳ w2
    εᴳ-respects-≈ = quot-rel ∘ GG.qwr-rel ∘ map-inl-respects-≈

  map-inl-preserves-++ : {w1 w2 : List A} → map inl (w1 ++ w2) ≈ᴳ map inl w1 ++ map inl w2
  map-inl-preserves-++ {w1} {w2} =
    transport (GRel _) (map-++ inl w1 w2) (≈-refl (map codiag (map inl (w1 ++ w2))))

  abstract
    εᴳ-preserves-comp : {w1 w2 : List A} → εᴳ (w1 ++ w2) == Group.comp G (εᴳ w1) (εᴳ w2)
    εᴳ-preserves-comp {w1} {w2} = quot-rel (GG.qwr-rel (map-inl-preserves-++ {w1} {w2}))

  ε : SG →ᴳ G
  GroupHom.f ε = SetQuot-rec εᴳ εᴳ-respects-≈
  GroupHom.pres-comp ε =
    SetQuot-elim (λ w1 → SetQuot-elim (λ w2 →
      εᴳ-preserves-comp {w1} {w2})
        (λ r → prop-has-all-paths-↓))
          (λ r → prop-has-all-paths-↓)
