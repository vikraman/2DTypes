\begin{code}[hide]
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
open import Pi+.Indexed.Translation
import Pi+.Indexed.Equiv1 as Pi+
import Pi+.Indexed.Equiv0Hat as Pi^
import Pi+.Indexed.Equiv1Hat as Pi^
import Pi+.Indexed.Equiv0Norm as Pi^
import Pi+.Indexed.Equiv1Norm as Pi^
open import Pi+.UFin
open import Pi+.UFin.Monoidal
open import Pi+.Common.FinHelpers
open import Pi+.Lehmer.FinHelpers

module Pi+.Indexed.ExamplesL where

private
  variable
    m n o p q r : ℕ

instance
  ltS : {m : ℕ} → m N.< (S m)
  ltS = N.ltS
  ltSR : {m n : ℕ} → {{m N.< n}} → m N.< (S n)
  ltSR {m} {n} {{ϕ}} = N.ltSR ϕ

⟦_⟧ : Pi.U → Type₀
⟦ O ⟧ = ⊥
⟦ I ⟧ = ⊤
⟦ t₁ + t₂ ⟧ = ⟦ t₁ ⟧ ⊔ ⟦ t₂ ⟧
⟦ t₁ × t₂ ⟧ = ⟦ t₁ ⟧ S.× ⟦ t₂ ⟧

⟦-⟧-eval₀ : {X : Pi.U} → ⟦ X ⟧ ≃ Fin (eval₀ X)
⟦-⟧-eval₀ {O} =
  Fin-equiv-Empty ⁻¹
⟦-⟧-eval₀ {I} =
  contr-equiv-Unit Fin1-level ⁻¹
⟦-⟧-eval₀ {t₁ + t₂} =
  Fin-⊔ {eval₀ t₁} {eval₀ t₂} ∘e
  ⊔-≃ (⟦-⟧-eval₀ {t₁}) (⟦-⟧-eval₀ {t₂})
⟦-⟧-eval₀ {t₁ × t₂} =
  Fin-× {eval₀ t₁} {eval₀ t₂} ∘e
  ×-≃ (⟦-⟧-eval₀ {t₁}) (⟦-⟧-eval₀ {t₂})

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

test0 : ⟦ 𝟚 Pi.+ 𝟚 ⟧ → Fin 4
test0 = –> ⟦-⟧-eval₀

_ : (test0 (inr (inr tt)) == 0) S.×
    (test0 (inr (inl tt)) == 1) S.×
    (test0 (inl (inr tt)) == 2) S.×
    (test0 (inl (inl tt)) == 3)
_ = fin= idp , fin= idp , fin= idp , fin= idp

test1 : ⟦ 𝔹 2 ⟧ → Fin 4
test1 = –> ⟦-⟧-eval₀

_ : (test1 (inr tt , inr tt) == 0) S.×
    (test1 (inr tt , inl tt) == 1) S.×
    (test1 (inl tt , inr tt) == 2) S.×
    (test1 (inl tt , inl tt) == 3)
_ = fin= idp , fin= idp , fin= idp , fin= idp

interp' : {X : Pi.U} (c : X Pi.⟷₁ X) → ⟦ X ⟧ ≃ ⟦ X ⟧
interp' c = ⟦-⟧-eval₀ ⁻¹ ∘e Pi^.evalNorm₁ (eval₁ c) ∘e ⟦-⟧-eval₀

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

_ : (cnot^p 0 == 0) S.× (cnot^p 1 == 1) S.× (cnot^p 2 == 3) S.× (cnot^p 3 == 2)
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
        f (O , ϕ) = 0
        f (1 , ϕ) = 1
        f (2 , ϕ) = 3
        f (3 , ϕ) = 2
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

-- copy(𝔽,b₁,…,bₙ) = (b₁,b₁,…,bₙ)
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
reset (S (S n)) = rearrange 𝟚 𝟚 (𝔹 (S n)) ◎ cif (not ⊗ id⟷₁) (reset (S n)) ◎ rearrange 𝟚 𝟚 (𝔹 (S n))
\end{code}

\newcommand{\resetthree}{%
\begin{code}
reset3 : 𝟚 Pi.× 𝔹 3 Pi.⟷₁ 𝟚 Pi.× 𝔹 3
reset3 =
  (assocl⋆ ◎ (swap⋆ ⊗ id⟷₁) ◎ assocr⋆) ◎
  (dist ◎
   ((id⟷₁ ⊗ (swap₊ ⊗ id⟷₁)) ⊕
    (id⟷₁ ⊗
     ((assocl⋆ ◎ (swap⋆ ⊗ id⟷₁) ◎ assocr⋆) ◎
      (dist ◎
       ((id⟷₁ ⊗ (swap₊ ⊗ id⟷₁)) ⊕
        (id⟷₁ ⊗
         (swap⋆ ◎ (dist ◎ ((id⟷₁ ⊗ swap₊) ⊕ id⟷₁) ◎ factor) ◎ swap⋆)))
       ◎ factor)
      ◎ assocl⋆ ◎ (swap⋆ ⊗ id⟷₁) ◎ assocr⋆)))
   ◎ factor)
  ◎ assocl⋆ ◎ (swap⋆ ⊗ id⟷₁) ◎ assocr⋆
\end{code}}

\begin{code}[hide]
reset^ : ∀ n → _
reset^ = eval₁ ∘ reset

reset+ : ∀ n → _
reset+ = Pi^.quote^₁ ∘ Pi^.quoteNorm₁ idp ∘ Pi^.evalNorm₁ ∘ reset^
\end{code}

\newcommand{\resetnormthree}{%
\begin{code}
reset+3 : Pi^.quote^₀ 16 Pi+.⟷₁ Pi^.quote^₀ 16
reset+3 =
  (id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊)
  ◎
  (id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊)
  ◎
  (id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕
   id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊)
  ◎ id⟷₁
\end{code}}


\begin{code}[hide]
-- reset+test : Fin 4 → Fin 4
-- reset+test = –> (Pi+.eval₁ (reset+ 1))

-- reset+test-0 : reset+test 0 == 0 -- 00 -> 00
-- reset+test-0 = fin= idp

-- reset+test-1 : reset+test 1 == 3 -- 10 -> 11
-- reset+test-1 = fin= idp

-- reset+test-2 : reset+test 2 == 2 -- 01 -> 01
-- reset+test-2 = fin= idp

-- reset+test-3 : reset+test 3 == 1 -- 11 -> 10
-- reset+test-3 = fin= idp

reset+test : Fin 16 → Fin 16
reset+test = –> (Pi+.eval₁ (reset+ 3))

reset-test : Fin 16 → Fin 16
reset-test = –> (Pi^.evalNorm₁ (eval₁ (reset 3)))

-- 0 b1 b2 b3 => or(b1,b2,b3) , b1 b2 b3
-- 1 b1 b2 b3 => nor(b1,b2,b3) , b1 b2 b3

-- {-

-- 0000 -> 0000 -> 0 -> 0
-- 0001 -> 1001 -> 1 -> 9
-- 0010 -> 1010 -> 2 -> 10
-- 0011 -> 1011 -> 3 -> 11
-- 0100 -> 1100 -> 4 -> 12
-- 0101 -> 1101 -> 5 -> 13
-- 0110 -> 1110 -> 6 -> 14
-- 0111 -> 1111 -> 7 -> 15
-- 1000 -> 1000 -> 8 -> 8
-- 1001 -> 0001 -> 9 -> 1
-- 1010 -> 0010 -> 10 -> 2
-- 1011 -> 0011 -> 11 -> 3
-- 1100 -> 0100 -> 12 -> 4
-- 1101 -> 0101 -> 13 -> 5
-- 1110 -> 0110 -> 14 -> 6
-- 1111 -> 0111 -> 15 -> 7

-- -}

_ : reset-test 5 == 5
_ = fin= idp

reset+test-0 : reset+test 0 == 0 -- 0000 -> 0000
reset+test-0 = fin= idp

reset+test-1 : reset+test 1 == 3 -- 1000 -> 1001
reset+test-1 = fin= idp

reset+test-2 : reset+test 2 == 2 -- 0100 -> 0100
reset+test-2 = fin= idp

reset+test-3 : reset+test 3 == 1 -- 1001 -> 1000
reset+test-3 = fin= idp

reset+test-4 : reset+test 4 == 4
reset+test-4 = fin= idp

reset+test-5 : reset+test 5 == 5
reset+test-5 = fin= idp

reset+test-6 : reset+test 6 == 6
reset+test-6 = fin= idp

reset+test-7 : reset+test 7 == 7
reset+test-7 = fin= idp

reset+test-8 : reset+test 8 == 8
reset+test-8 = fin= idp

reset+test-9 : reset+test 9 == 9
reset+test-9 = fin= idp

reset+test-n : reset+test 12 == 12
reset+test-n = fin= idp

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

incr+test : Fin 4 → Fin 4
incr+test = –> (Pi+.eval₁ (incr+ 2))

incr+test-0 : incr+test 0 == 3
incr+test-0 = fin= idp

incr+test-1 : incr+test 1 == 0
incr+test-1 = fin= idp

incr+test-2 : incr+test 2 == 1
incr+test-2 = fin= idp

incr+test-3 : incr+test 3 == 2
incr+test-3 = fin= idp
\end{code}