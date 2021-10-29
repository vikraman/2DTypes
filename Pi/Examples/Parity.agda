{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi.Examples.Parity where

open import HoTT as S
open import Pi.Syntax.Pi^ as Pi^
open import Pi.Syntax.Pi^Helpers as Pi^
import Pi.Equiv.Equiv0Hat as Pi^
import Pi.Equiv.Equiv1Hat as Pi^
import Pi.Equiv.Equiv0Norm as Pi^
import Pi.Equiv.Equiv1Norm as Pi^

open import Pi.Equiv.Equiv1NormHelpers using (pi^2list)
open import Pi.Coxeter.Coxeter
open import Pi.Equiv.Equiv2Norm using (evalNorm₂)
open import Pi.Lehmer.Lehmer2FinEquiv using (Fin≃Lehmer)
open import Pi.Lehmer.Lehmer2 using (Lehmer1-Lehmer2-equiv)
open import Pi.Coxeter.Lehmer2CoxeterEquiv using (immersion ; immersion∘immersion⁻¹)

-- inl is true
B : _
B = ⊤ ⊔ ⊤

negate : B → B
negate true = false
negate false = true

plus : B → B → B
plus true true = true
plus true false = false
plus false true = false
plus false false = true

negate-plus : (x y : B) → negate (plus x y) == plus (negate x) y
negate-plus true true = idp
negate-plus true false = idp
negate-plus false true = idp
negate-plus false false = idp

module _ {i} {A : Type i} where

  list-len-parity : List A → ⊤ ⊔ ⊤
  list-len-parity = foldr (λ _ → negate) true

  list-len-parity-++ : (l₁ l₂ : List A) → (list-len-parity (l₁ ++ l₂)) == plus (list-len-parity l₁) (list-len-parity l₂)
  list-len-parity-++ nil l with (list-len-parity l)
  ... | true = idp
  ... | false = idp
  list-len-parity-++ (x :: l₁) l₂ rewrite (list-len-parity-++ l₁ l₂) = negate-plus _ _

parity : {n m : ℕ} → (c : S n Pi^.⟷₁^ S m) → ⊤ ⊔ ⊤
parity {X} {Y} c =
 let s = pi^2list c
 in list-len-parity s

idp-refl : {m : ℕ} {l₁ l₂ : List (Fin m)} → (l₁ == l₂) -> l₁ ≈* l₂
idp-refl idp = idp

≃*-preserved : {n : ℕ} → {c₁ c₂ : S n Pi^.⟷₁^ S n} → (α : c₁ Pi^.⟷₂^ c₂) → pi^2list c₁ ≈* pi^2list c₂
≃*-preserved {c₁ = c₁} {c₂ = c₂} α =
  let r = ap (–> Fin≃Lehmer) (evalNorm₂ α)
      s₁ = <– Lehmer1-Lehmer2-equiv (Pi^.pi^2lehmer c₁)
      s₂ = <– Lehmer1-Lehmer2-equiv (Pi^.pi^2lehmer c₂)
      q = (! (<–-inv-r Fin≃Lehmer ((Pi^.pi^2lehmer c₁)))) ∙ r ∙ (<–-inv-r Fin≃Lehmer ((Pi^.pi^2lehmer c₂)))
      w = ap immersion q
      o₁ = immersion∘immersion⁻¹ (pi^2list c₁)
      o₂ = immersion∘immersion⁻¹ (pi^2list c₂)
  in   comm o₁ ■ idp-refl w ■ o₂

≃*-preserves-parity : {m : ℕ} → {l₁ l₂ : List (Fin m)} → (l₁ ≈* l₂) → (list-len-parity l₁ == list-len-parity l₂)
≃*-preserves-parity idp = idp
≃*-preserves-parity (comm q) = ! (≃*-preserves-parity q)
≃*-preserves-parity (trans q q₁) = ≃*-preserves-parity q ∙ ≃*-preserves-parity q₁
≃*-preserves-parity (respects-++ {l = l} {l'} {r = r} {r'} q q₁)
  rewrite (list-len-parity-++ l r)
  rewrite (list-len-parity-++ l' r')
  rewrite (≃*-preserves-parity q)
  rewrite (≃*-preserves-parity q₁) = idp
≃*-preserves-parity (≈-rel (swap x)) = idp
≃*-preserves-parity (≈-rel braid) = idp
≃*-preserves-parity (≈-rel cancel) = idp

parity-preserved : {n : ℕ} → (c₁ c₂ : S n Pi^.⟷₁^ S n) → (α : c₁ Pi^.⟷₂^ c₂) → parity c₁ == parity c₂
parity-preserved c₁ c₂ α =
  let s₁ = pi^2list c₁
      s₂ = pi^2list c₂
  in  ≃*-preserves-parity (≃*-preserved α)

parity-preserved-composition : {n m : ℕ} → (c d : S n Pi^.⟷₁^ S n) → (parity c == inl tt) → (parity d == inl tt) → parity (c ◎^ d) == inl tt
parity-preserved-composition c d p q rewrite (list-len-parity-++ (pi^2list c) (pi^2list d)) rewrite p rewrite q = idp

n-comp : {m : ℕ} → (n : ℕ) → (c : S m Pi^.⟷₁^ S m) → S m Pi^.⟷₁^ S m
n-comp O c = id⟷₁^
n-comp (S n) c = c ◎^ (n-comp n c)

parity-preserved-arbitrary : {m : ℕ} → (n : ℕ) → (c : S m Pi^.⟷₁^ S m) → parity c == inl tt → parity (n-comp n c) == inl tt
parity-preserved-arbitrary O c p = idp
parity-preserved-arbitrary {m = m} (S n) c p =
  let r = parity-preserved-composition {m = m} c (n-comp {m} n c) p
  in  r (parity-preserved-arbitrary n c p)

open import Pi.Equiv.Translation2 using (eval₁)
open import Pi.Equiv.Equiv1Hat using (eval^₁)
open import Pi.Examples.Adder
open import Pi.Examples.Reset
open import Pi.Examples.Toffoli
open import Pi.Syntax.Pi as Pi
open import Pi.Examples.Base

_ : parity (eval₁ adder3) == false
_ = idp

_ : parity (eval₁ (reset 2)) == false
_ = idp

_ : parity (eval^₁ reset2-perm+) == false
_ = idp

_ : parity (eval₁ adder4) == false
_ = idp

_ : parity (eval₁ (reset 3)) == false
_ = idp

toffoli₄¹ toffoli₄² toffoli₄³ toffoli₄⁴ toffoli₄⁵ toffoli₄⁶ toffoli₄⁷ toffoli₄⁸ : 𝔹 4 ⟷₁ 𝔹 4
toffoli₄¹ = cif (cif (swap₊ ⊗ id⟷₁) (id⟷₁ ⊗ id⟷₁)) (id⟷₁ ⊗ (id⟷₁ ⊗ id⟷₁))
toffoli₄² = cif (cif (id⟷₁ ⊗ swap₊) (id⟷₁ ⊗ id⟷₁)) (id⟷₁ ⊗ (id⟷₁ ⊗ id⟷₁))
toffoli₄³ = cif (cif (id⟷₁ ⊗ id⟷₁) (swap₊ ⊗ id⟷₁)) (id⟷₁ ⊗ (id⟷₁ ⊗ id⟷₁))
toffoli₄⁴ = cif (cif (id⟷₁ ⊗ id⟷₁) (id⟷₁ ⊗ swap₊)) (id⟷₁ ⊗ (id⟷₁ ⊗ id⟷₁))
toffoli₄⁵ = cif (cif (id⟷₁ ⊗ id⟷₁) (id⟷₁ ⊗ id⟷₁)) (id⟷₁ ⊗ (id⟷₁ ⊗ id⟷₁))
toffoli₄⁶ = cif (cif (id⟷₁ ⊗ id⟷₁) (id⟷₁ ⊗ id⟷₁)) (swap₊ ⊗ (id⟷₁ ⊗ id⟷₁))
toffoli₄⁷ = cif (cif (id⟷₁ ⊗ id⟷₁) (id⟷₁ ⊗ id⟷₁)) (id⟷₁ ⊗ (swap₊ ⊗ id⟷₁))
toffoli₄⁸ = cif (cif (id⟷₁ ⊗ id⟷₁) (id⟷₁ ⊗ id⟷₁)) (id⟷₁ ⊗ (id⟷₁ ⊗ swap₊))

_ : parity (eval₁ toffoli₄) == false
_ = idp

_ : (parity (eval₁ toffoli₄¹) == true) S.×
    (parity (eval₁ toffoli₄²) == true) S.×
    (parity (eval₁ toffoli₄³) == true) S.×
    (parity (eval₁ toffoli₄⁴) == true) S.×
    (parity (eval₁ toffoli₄⁵) == true) S.×
    (parity (eval₁ toffoli₄⁶) == true) S.×
    (parity (eval₁ toffoli₄⁷) == true) S.×
    (parity (eval₁ toffoli₄⁸) == true)
_ = idp , idp , idp , idp , idp , idp , idp , idp

parity-toffoli₄-comp : (n : ℕ) (c : 𝔹 4 ⟷₁ 𝔹 4) (_ : parity (eval₁ c) == true)
                     → parity (n-comp n (eval₁ c)) == parity (eval₁ toffoli₄) → ⊥
parity-toffoli₄-comp n c ϕ p =
  let q = parity-preserved-arbitrary n (eval₁ c) ϕ
      r = ! q ∙ p
  in Bool-true≠false r
