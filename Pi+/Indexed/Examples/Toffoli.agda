{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

open import HoTT hiding (_<_ ; ltS ; ltSR ; _+_ ; _×_)
import lib.types.Nat as N
import lib.types.Sigma as S

open import Pi+.UFin.BAut
open import Pi+.Misc
open import Pi+.Extra

open import Pi+.Indexed.Syntax as Pi+
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.Indexed.SyntaxHatHelpers as Pi^
open import Pi+.Indexed.SyntaxFull as Pi
open import Pi+.Indexed.Translation2
import Pi+.Indexed.Equiv1 as Pi+
import Pi+.Indexed.Equiv0Hat as Pi^
import Pi+.Indexed.Equiv1Hat as Pi^
import Pi+.Indexed.Equiv0Norm as Pi^
import Pi+.Indexed.Equiv1Norm as Pi^
open import Pi+.UFin
open import Pi+.UFin.Monoidal
open import Pi+.Common.FinHelpers
open import Pi+.Lehmer.FinHelpers

module Pi+.Indexed.Examples.Toffoli where

open import Pi+.Indexed.Examples.Base

-- NOTE: Left is True

swap2 : 𝔹 2 Pi.⟷₁ 𝔹 2
swap2 = swap⋆

_ : (–> (interp' swap2) (inr tt , inr tt) == inr tt , inr tt) S.×
    (–> (interp' swap2) (inr tt , inl tt) == inl tt , inr tt) S.×
    (–> (interp' swap2) (inl tt , inr tt) == inr tt , inl tt) S.×
    (–> (interp' swap2) (inl tt , inl tt) == inl tt , inl tt)
_ = idp , idp , idp , idp

controlled : {t : Pi.U} → (c : t Pi.⟷₁ t) → (𝟚 Pi.× t Pi.⟷₁ 𝟚 Pi.× t)
controlled c = dist ◎ ((id⟷₁ ⊗ c) ⊕ id⟷₁) ◎ factor

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

not^p : Fin 2 → Fin 2
not^p = –> (Pi^.evalNorm₁ not^)

_ : (not^p 0 == 1) S.× (not^p 1 == 0)
_ = fin= idp , fin= idp

cnot : 𝟚 Pi.× 𝟚 Pi.⟷₁ 𝟚 Pi.× 𝟚
cnot = controlled not

cnot^ : 4 ⟷₁^ 4
cnot^ = eval₁ cnot

cnot^p : Fin 4 → Fin 4
cnot^p = –> (Pi^.evalNorm₁ cnot^)

_ : (cnot^p 0 == 1) S.× (cnot^p 1 == 0) S.× (cnot^p 2 == 2) S.× (cnot^p 3 == 3)
_ = fin= idp , fin= idp , fin= idp , fin= idp

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
        f (O , ϕ) = 1
        f (1 , ϕ) = 0
        f (2 , ϕ) = 2
        f (3 , ϕ) = 3
        f (n , N.ltSR (N.ltSR (N.ltSR (N.ltSR ()))))
        f-f : (x : Fin 4) → f (f x) == x
        f-f (O , ϕ) = fin= idp
        f-f (1 , ϕ) = fin= idp
        f-f (2 , ϕ) = fin= idp
        f-f (3 , ϕ) = fin= idp
        f-f (n , N.ltSR (N.ltSR (N.ltSR (N.ltSR ()))))

toffoli^2perm=swap23 : toffoli^2-perm == swap23
toffoli^2perm=swap23 = e= ϕ
  where ϕ : (f : Fin 4) → –> toffoli^2-perm f == –> swap23 f
        ϕ (O , ϕ) = fin= idp
        ϕ (1 , ϕ) = fin= idp
        ϕ (2 , ϕ) = fin= idp
        ϕ (3 , ϕ) = fin= idp
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

swap67 : Aut (Fin 8)
swap67 = equiv f f f-f f-f
  where f : Fin 8 → Fin 8
        f (O , ϕ) = 1
        f (1 , ϕ) = 0
        f (2 , ϕ) = 2
        f (3 , ϕ) = 3
        f (4 , ϕ) = 4
        f (5 , ϕ) = 5
        f (6 , ϕ) = 6
        f (7 , ϕ) = 7
        f (n , N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR ()))))))))
        f-f : (x : Fin 8) → f (f x) == x
        f-f (O , ϕ) = fin= idp
        f-f (1 , ϕ) = fin= idp
        f-f (2 , ϕ) = fin= idp
        f-f (3 , ϕ) = fin= idp
        f-f (4 , ϕ) = fin= idp
        f-f (5 , ϕ) = fin= idp
        f-f (6 , ϕ) = fin= idp
        f-f (7 , ϕ) = fin= idp
        f-f (n , N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR ()))))))))

swap67+ : _ Pi+.⟷₁ _
swap67+ = Pi^.quote^₁ (Pi^.quoteNorm₁ idp swap67)
