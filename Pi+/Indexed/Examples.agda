{-# OPTIONS --without-K --exact-split --rewriting #-}

open import lib.Base
open import lib.Equivalence
open import lib.NType
import lib.types.Nat as N
open import lib.types.Fin

open import Pi+.UFin.BAut
open import Pi+.Misc
open import Pi+.Extra

module Pi+.Indexed.Examples where

open import Pi+.Indexed.Syntax as Pi+
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.Indexed.SyntaxHatHelpers as Pi^
open import Pi+.Indexed.SyntaxFull as Pi
open import Pi+.Indexed.Translation
import Pi+.Indexed.Equiv1 as Pi+
import Pi+.Indexed.Equiv1Hat as Pi^
import Pi+.Indexed.Equiv1Norm as Pi^

private
  variable
    m n o p q r : ℕ

𝟚 : Pi.U
𝟚 = I + I

𝟜+ : Pi+.U 4
𝟜+ = I + I + I + I + O

𝟠+ : Pi+.U 8
𝟠+ = I + I + I + I + I + I + I + I + O

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

toffoli₃ : 𝟚 Pi.× (𝟚 Pi.× 𝟚) Pi.⟷₁ 𝟚 Pi.× (𝟚 Pi.× 𝟚)
toffoli₃ = controlled cnot

toffoli₃^ : 8 ⟷₁^ 8
toffoli₃^ = eval₁ toffoli₃

toffoli : ∀ n → 𝔹 n Pi.⟷₁ 𝔹 n
toffoli O = id⟷₁
toffoli (S O) = swap₊
toffoli (S (S n)) = cif (toffoli (S n)) id⟷₁

toffoli^ : ∀ n → _
toffoli^ = eval₁ ∘ toffoli

toffoli+ : ∀ n → _
toffoli+ = Pi^.quote^₁ ∘ Pi^.quoteNorm₁ idp ∘ Pi^.evalNorm₁ ∘ toffoli^

toffoli^2-perm : Aut (Fin 4)
toffoli^2-perm = Pi^.evalNorm₁ (toffoli^ 2)

swap23 : Aut (Fin 4)
swap23 = equiv f f f-f f-f
  where f : Fin 4 → Fin 4
        f (O , ϕ) = O , ϕ
        f (1 , ϕ) = 1 , ϕ
        f (2 , ϕ) = 3 , N.ltS
        f (3 , ϕ) = 2 , N.ltSR N.ltS
        f (n , N.ltSR (N.ltSR (N.ltSR (N.ltSR ()))))
        f-f : (x : Fin 4) → f (f x) == x
        f-f (O , ϕ) = idp
        f-f (1 , ϕ) = idp
        f-f (2 , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (3 , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (n , N.ltSR (N.ltSR (N.ltSR (N.ltSR ()))))

toffoli^2perm=swap23 : toffoli^2-perm == swap23
toffoli^2perm=swap23 = e= ϕ
  where ϕ : (f : Fin 4) → _
        ϕ (O , ϕ) = pair= idp (prop-has-all-paths _ _)
        ϕ (1 , ϕ) = pair= idp (prop-has-all-paths _ _)
        ϕ (2 , ϕ) = pair= idp (prop-has-all-paths _ _)
        ϕ (3 , ϕ) = pair= idp (prop-has-all-paths _ _)
        ϕ (n , N.ltSR (N.ltSR (N.ltSR (N.ltSR ()))))

swap23^ : 4 Pi^.⟷₁^ 4
swap23^ = Pi^.quoteNorm₁ idp swap23

toffoli^2=swap23^ : toffoli^ 2 Pi^.⟷₂^ swap23^
toffoli^2=swap23^ = (((c₂ ⊡^ c₂) ⊡^ ((c₃ ⊡^ (c₄ ⊡^ (c₂ ⊡^ c₂))) ⊡^ (c₂ ⊡^ c₂))) ■^
                    (idl◎l^ ⊡^ (idl◎l^ ⊡^ idl◎l^)) ■^
                    idl◎l^ ■^ idr◎l^ ■^ assoc◎l^ ■^ idr◎l^ ■^ idr◎l^) ■^ idr◎r^
  where c₂ : ⊕^ ⊕^ id⟷₁^ ⟷₂^ id⟷₁^
        c₂ = (resp⊕⟷₂ ⊕id⟷₁⟷₂^) ■^ ⊕id⟷₁⟷₂^
        c₃ : (⊕^ ⊕^ ⊕^ ⊕^ id⟷₁^) ⟷₂^ id⟷₁^
        c₃ = resp⊕⟷₂ (resp⊕⟷₂ (resp⊕⟷₂ ⊕id⟷₁⟷₂^)) ■^
             resp⊕⟷₂ (resp⊕⟷₂ ⊕id⟷₁⟷₂^) ■^
             resp⊕⟷₂ ⊕id⟷₁⟷₂^ ■^
             ⊕id⟷₁⟷₂^
        c₄ : (swap₊^ ◎^ ⊕^ ⊕^ id⟷₁^) ⟷₂^ swap₊^
        c₄ = (id⟷₂^ ⊡^ c₂) ■^ idr◎l^

swap23+ : 𝟜+ Pi+.⟷₁ 𝟜+
swap23+ = Pi+.quote₁ idp swap23

toffoli2+ : 𝟜+ Pi+.⟷₁ 𝟜+
toffoli2+ = Pi^.quote^₁ swap23^

copy : ∀ n → 𝟚 Pi.× 𝔹 n Pi.⟷₁ 𝟚 Pi.× 𝔹 n
copy O = id⟷₁
copy (S O) = swap⋆ ◎ cnot ◎ swap⋆
copy (S (S n)) = assocl⋆ ◎ (copy (S O) ⊗ id⟷₁) ◎ assocr⋆

copy^ : ∀ n → _
copy^ = eval₁ ∘ copy

copy+ : ∀ n → _
copy+ = Pi^.quote^₁ ∘ Pi^.quoteNorm₁ idp ∘ Pi^.evalNorm₁ ∘ copy^

rearrange : (t₁ t₂ t₃ : Pi.U) → t₁ Pi.× (t₂ Pi.× t₃) Pi.⟷₁ t₂ Pi.× (t₁ Pi.× t₃)
rearrange t₁ t₂ t₃ = assocl⋆ ◎ (swap⋆ ⊗ id⟷₁) ◎ assocr⋆

reset : ∀ n → 𝟚 Pi.× 𝔹 n Pi.⟷₁ 𝟚 Pi.× 𝔹 n
reset O = id⟷₁
reset (S O) = swap⋆ ◎ cnot ◎ swap⋆
reset (S (S n)) = rearrange 𝟚 𝟚 (𝔹 (S n)) ◎ cif (reset (S n)) (swap₊ ⊗ id⟷₁) ◎ rearrange 𝟚 𝟚 (𝔹 (S n))

reset^ : ∀ n → _
reset^ = eval₁ ∘ reset

reset+ : ∀ n → _
reset+ = Pi^.quote^₁ ∘ Pi^.quoteNorm₁ idp ∘ Pi^.evalNorm₁ ∘ reset^

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

incr+ : ∀ n → _
incr+ = Pi^.quote^₁ ∘ Pi^.quoteNorm₁ idp ∘ Pi^.evalNorm₁ ∘ incr^
