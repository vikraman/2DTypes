{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import HoTT

open import Pi.Coxeter.Sn hiding (Sn)
open import Pi.Coxeter.Coxeter
open import Pi.Coxeter.Group
open import Pi.Extra
open import Pi.Misc

module Pi.Coxeter.GeneratedGroup (n : ℕ) where

  GRel : Rel (Word (Fin n)) lzero
  GRel w1 w2 = map codiag w1 ≈* map codiag w2

  syntax GRel w1 w2 = w1 ≈ᴳ w2

  module GG = GeneratedGroup (Fin n) GRel
  G = GG.GenGroup
  Sn = SnGroup n

  open GG.HomomorphismEquiv Sn

  ηˢ : Fin n → List (Fin n)
  ηˢ = _:: nil

  ηᴳ : Fin n → Group.El Sn
  ηᴳ = q[_] ∘ ηˢ

  PlusMinus-extendˢ : PlusMinus (Fin n) → List (Fin n)
  PlusMinus-extendˢ (inl a) = ηˢ a
  PlusMinus-extendˢ (inr a) = reverse (ηˢ a)

  PlusMinus-extendᴳ-η : ∀ w → PlusMinus-extendᴳ Sn ηᴳ w == q[ PlusMinus-extendˢ w ]
  PlusMinus-extendᴳ-η (inl a) = idp
  PlusMinus-extendᴳ-η (inr a) = idp

  Word-extendˢ : Word (Fin n) → List (Fin n)
  Word-extendˢ = foldr' _++_ nil ∘ map PlusMinus-extendˢ

  Word-extendˢ-η : ∀ w → Word-extendˢ w == map codiag w
  Word-extendˢ-η nil = idp
  Word-extendˢ-η (inl x :: nil) = idp
  Word-extendˢ-η (inr x :: nil) = idp
  Word-extendˢ-η (inl x :: w@(_ :: _)) = ap (x ::_) (Word-extendˢ-η w)
  Word-extendˢ-η (inr x :: w@(_ :: _)) = ap (x ::_) (Word-extendˢ-η w)

  Word-extendᴳ-η : ∀ w → Word-extendᴳ Sn ηᴳ w == q[ Word-extendˢ w ]
  Word-extendᴳ-η nil = idp
  Word-extendᴳ-η (x :: nil) =
      Word-extendᴳ-:: Sn ηᴳ x nil
    ∙ ap (λ l → Group.comp Sn l q[ nil ]) (PlusMinus-extendᴳ-η x)
    ∙ ap q[_] (++-unit-r (PlusMinus-extendˢ x))
  Word-extendᴳ-η (x :: w@(_ :: _)) =
      Word-extendᴳ-:: Sn ηᴳ x w
    ∙ ap2 (Group.comp Sn) (PlusMinus-extendᴳ-η x) (Word-extendᴳ-η w)

  η-respects-relˢ : ∀ {w1 w2} → GRel w1 w2 → Word-extendˢ w1 ≈* Word-extendˢ w2
  η-respects-relˢ {w1} {w2} r = transport2 _≈*_ (! (Word-extendˢ-η w1)) (! (Word-extendˢ-η w2)) r

  abstract
    η-respects-relᴳ : respects-rel ηᴳ
    η-respects-relᴳ {w1} {w2} r = Word-extendᴳ-η w1 ∙ quot-rel (η-respects-relˢ r) ∙ ! (Word-extendᴳ-η w2)

  module R = RelationRespectingFunctions (Fin n) GRel Sn
  open R.RelationRespectingFunction

  ηᴳ♯ : G →ᴳ Sn
  ηᴳ♯ = GG.HomomorphismEquiv.extend Sn (rel-res-fun ηᴳ η-respects-relᴳ)

  εᴳ : List (Fin n) → Group.El G
  εᴳ = q[_] ∘ map inl

  map-inl-respects-≈ : {w1 w2 : List (Fin n)} → w1 ≈* w2 → map inl w1 ≈ᴳ map inl w2
  map-inl-respects-≈ {nil} {nil} r =
    idp {n}
  map-inl-respects-≈ {nil} {x :: w2} r =
    transport (nil ≈*_) (ap (x ::_) (! (map-∘ inl codiag ∙ map-id))) r
  map-inl-respects-≈ {x :: w1} {nil} r =
    transport (_≈* nil) (ap (x ::_) (! (map-∘ inl codiag ∙ map-id))) r
  map-inl-respects-≈ {x :: w1} {y :: w2} r =
    transport2 _≈*_ (ap (x ::_) (! (map-∘ inl codiag ∙ map-id))) (ap (y ::_) (! (map-∘ inl codiag ∙ map-id))) r

  abstract
    εᴳ-respects-≈ : {w1 w2 : List (Fin n)} → w1 ≈* w2 → εᴳ w1 == εᴳ w2
    εᴳ-respects-≈ = quot-rel ∘ GG.qwr-rel ∘ map-inl-respects-≈

  map-inl-preserves-++ : {w1 w2 : List (Fin n)} → map inl (w1 ++ w2) ≈ᴳ map inl w1 ++ map inl w2
  map-inl-preserves-++ {w1} {w2} =
    transport (GRel _) (map-++ inl w1 w2) (idp {n})

  abstract
    εᴳ-preserves-comp : {w1 w2 : List (Fin n)} → εᴳ (w1 ++ w2) == Group.comp G (εᴳ w1) (εᴳ w2)
    εᴳ-preserves-comp {w1} {w2} = quot-rel (GG.qwr-rel (map-inl-preserves-++ {w1} {w2}))

  ε : Sn →ᴳ G
  GroupHom.f ε = SetQuot-rec εᴳ εᴳ-respects-≈
  GroupHom.pres-comp ε =
    SetQuot-elim (λ w1 → SetQuot-elim (λ w2 →
      εᴳ-preserves-comp {w1} {w2})
        (λ r → prop-has-all-paths-↓))
          (λ r → prop-has-all-paths-↓)
