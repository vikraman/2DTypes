{-# OPTIONS --without-K --exact-split --rewriting #-}

open import lib.Base
import lib.types.Nat as N

open import Pi+.Misc
open import Pi+.Extra

module Pi+.Indexed.Examples where

open import Pi+.Indexed.Syntax as Pi+
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.Indexed.SyntaxHatHelpers as Pi^
open import Pi+.Indexed.SyntaxFull as Pi
open import Pi+.Indexed.Translation

private
  variable
    m n o p q r : ℕ

𝟚 : Pi.U
𝟚 = I + I

𝔹 : ℕ → Pi.U
𝔹 O = I
𝔹 (S O) = 𝟚
𝔹 (S (S n)) = 𝟚 × 𝔹 (S n)

controlled : {t : Pi.U} → (c : t Pi.⟷₁ t) → (𝟚 Pi.× t Pi.⟷₁ 𝟚 Pi.× t)
controlled c = dist ◎ (id⟷₁ ⊕ (id⟷₁ ⊗ c)) ◎ factor

controlled^ : {t : Pi.U} → (c : t Pi.⟷₁ t) → _
controlled^ c = eval₁ (controlled c)

cif : {t : Pi.U} → (c₁ c₂ : t Pi.⟷₁ t) → (𝟚 Pi.× t Pi.⟷₁ 𝟚 Pi.× t)
cif c₁ c₂ = dist ◎ ((id⟷₁ ⊗ c₁) ⊕ (id⟷₁ ⊗ c₂)) ◎ factor

cif^ : {t : Pi.U} → (c₁ c₂ : t Pi.⟷₁ t) → _
cif^ c₁ c₂ = eval₁ (cif c₁ c₂)

not : 𝟚 Pi.⟷₁ 𝟚
not = swap₊

not^ : 2 Pi^.⟷₁^ 2
not^ = eval₁ not

cnot : 𝟚 Pi.× 𝟚 Pi.⟷₁ 𝟚 Pi.× 𝟚
cnot = controlled not

cnot^ : 4 ⟷₁^ 4
cnot^ = eval₁ cnot

toffoli₂ : 𝟚 Pi.× (𝟚 Pi.× 𝟚) Pi.⟷₁ 𝟚 Pi.× (𝟚 Pi.× 𝟚)
toffoli₂ = controlled cnot

toffoli₂^ : 8 ⟷₁^ 8
toffoli₂^ = eval₁ toffoli₂

toffoli : ∀ n → 𝔹 n Pi.⟷₁ 𝔹 n
toffoli O = id⟷₁
toffoli (S O) = swap₊
toffoli (S (S n)) = cif (toffoli (S n)) id⟷₁

toffoli^ : ∀ n → _
toffoli^ = eval₁ ∘ toffoli

copy : ∀ n → 𝟚 Pi.× 𝔹 n Pi.⟷₁ 𝟚 Pi.× 𝔹 n
copy O = id⟷₁
copy (S O) = swap⋆ ◎ cnot ◎ swap⋆
copy (S (S n)) = assocl⋆ ◎ (copy (S O) ⊗ id⟷₁) ◎ assocr⋆

copy^ : ∀ n → _
copy^ = eval₁ ∘ copy

rearrange : (t₁ t₂ t₃ : Pi.U) → t₁ Pi.× (t₂ Pi.× t₃) Pi.⟷₁ t₂ Pi.× (t₁ Pi.× t₃)
rearrange t₁ t₂ t₃ = assocl⋆ ◎ (swap⋆ ⊗ id⟷₁) ◎ assocr⋆

reset : ∀ n → 𝟚 Pi.× 𝔹 n Pi.⟷₁ 𝟚 Pi.× 𝔹 n
reset O = id⟷₁
reset (S O) = swap⋆ ◎ cnot ◎ swap⋆
reset (S (S n)) = rearrange 𝟚 𝟚 (𝔹 (S n)) ◎ cif (reset (S n)) (swap₊ ⊗ id⟷₁) ◎ rearrange 𝟚 𝟚 (𝔹 (S n))

reset^ : ∀ n → _
reset^ = eval₁ ∘ reset

fst2last : ∀ n → 𝔹 n Pi.⟷₁ 𝔹 n
fst2last O = id⟷₁
fst2last (S O) = id⟷₁
fst2last (S (S O)) = swap⋆
fst2last (S (S (S n))) = rearrange 𝟚 𝟚 (𝔹 (S n)) ◎ (id⟷₁ ⊗ fst2last (S (S n)))

incr : ∀ n → 𝔹 n Pi.⟷₁ 𝔹 n
incr O = id⟷₁
incr (S O) = swap₊
incr (S (S n)) = (id⟷₁ ⊗ incr (S n)) ◎ fst2last (S (S n)) ◎ toffoli (S (S n)) ◎ Pi.!⟷₁ (fst2last (S (S n)))

incr^ : ∀ n → _
incr^ = eval₁ ∘ incr
