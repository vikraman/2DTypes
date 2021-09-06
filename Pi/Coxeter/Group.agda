{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

module Pi.Coxeter.Group where

open import HoTT

open import Pi.Coxeter.Coxeter
open import Pi.Coxeter.Sn
open import Pi.Misc
open import Pi.Extra

module _ (n : ℕ) where

  SnGroupStructure : GroupStructure (Sn n)
  GroupStructure.ident SnGroupStructure =
    q[ nil ]
  GroupStructure.inv SnGroupStructure =
    SetQuot-map reverse (reverse-respects-≈ {n = n})
  GroupStructure.comp SnGroupStructure =
    SetQuot-map2 _++_ (λ l → idp) respects-++
  GroupStructure.unit-l SnGroupStructure =
    SetQuot-elim (λ l → idp) (λ p → prop-has-all-paths-↓)
  GroupStructure.assoc SnGroupStructure =
    SetQuot-elim (λ l1 → SetQuot-elim (λ l2 → SetQuot-elim (λ l3 →
      ap q[_] (++-assoc l1 l2 l3))
        (λ r → prop-has-all-paths-↓))
          (λ r → prop-has-all-paths-↓))
            (λ r → prop-has-all-paths-↓)
  GroupStructure.inv-l SnGroupStructure =
    SetQuot-elim (λ l → quot-rel (≈-inv-l l)) (λ r → prop-has-all-paths-↓)

  SnGroup : Group lzero
  Group.El SnGroup = Sn n
  Group.El-level SnGroup = ⟨⟩
  Group.group-struct SnGroup = SnGroupStructure
