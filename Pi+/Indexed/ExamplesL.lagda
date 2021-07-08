\begin{code}[hide]
{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}
module Pi+.Indexed.ExamplesL where

open import HoTT hiding (_<_ ; ltS ; ltSR ; _+_ ; _×_)
import lib.types.Nat as N
import lib.types.Sigma as S

open import Pi+.UFin.BAut
open import Pi+.Misc
open import Pi+.Extra

open import Pi+.Indexed.Syntax as Pi+
  renaming (_⟷₁_ to _⟷₁₊_; _⟷₂_ to _⟷₂₊_; !⟷₁ to !⟷₁₊; U to U+;
  idr◎l to idr◎l+; swapl₊⟷₂ to swapl₊⟷₂+)
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

open import Pi+.Indexed.Examples.Base
open import Pi+.Indexed.Examples.Toffoli hiding (cif)
open import Pi+.Indexed.Examples.Reset hiding (reset; reset2-perm)

private
  variable
    A B C D E F : U
\end{code}

\newcommand{\cif}{%
\begin{code}
cif : (c₁ c₂ : A ⟷₁ A) → (𝟚 × A ⟷₁ 𝟚 × A)
cif c₁ c₂ = dist ◎ ((id⟷₁ ⊗ c₁) ⊕ (id⟷₁ ⊗ c₂)) ◎ factor
\end{code}}

\newcommand{\resetn}{%
\begin{code}
reset : ∀ n → 𝟚 × 𝔹 n ⟷₁ 𝟚 × 𝔹 n
reset 0 = id⟷₁
reset 1 = swap⋆ ◎ cnot ◎ swap⋆
reset (S (S n)) = rearrange 𝟚 𝟚 (𝔹 (S n)) ◎ cif (not ⊗ id⟷₁) (reset (S n)) ◎ rearrange 𝟚 𝟚 (𝔹 (S n))
\end{code}}

\newcommand{\resetnormtwo}{%
\begin{code}
reset2Norm : 𝟠+ ⟷₁₊ 𝟠+
reset2Norm =  (id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
              (id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
              (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
              (id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
              (id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
              (id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
              (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
              (id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
              (id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
              (id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
              (id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
              (id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
              (id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
              (id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
              (id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ id⟷₁
\end{code}}

\newcommand{\resetperm}{%
\begin{code}
reset2-perm : Aut (Fin 8)
reset2-perm = equiv f f f-f f-f
  where f : Fin 8 → Fin 8
        f = lookup (0 :: 5 :: 6 :: 7 :: 4 :: 1 :: 2 :: 3 :: nil)
        f-f : (x : Fin 8) → f (f x) == x
        -- elided
\end{code}}
\begin{code}[hide]
        f-f (0 , ϕ) = fin= idp
        f-f (1 , ϕ) = fin= idp
        f-f (2 , ϕ) = fin= idp
        f-f (3 , ϕ) = fin= idp
        f-f (4 , ϕ) = fin= idp
        f-f (5 , ϕ) = fin= idp
        f-f (6 , ϕ) = fin= idp
        f-f (7 , ϕ) = fin= idp
        f-f (n , N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR ()))))))))

ccx = toffoli 3
cx = cnot
x = not

A[BC]-C[BA] : {A B C : U} → A × (B × C) ⟷₁ C × (B × A)
A[BC]-C[BA] = swap⋆ ◎ (swap⋆ ⊗ id⟷₁) ◎ assocr⋆

A[BC]-B[AC] : {t₁ t₂ t₃ : Pi.U} → t₁ Pi.× (t₂ Pi.× t₃) Pi.⟷₁ t₂ Pi.× (t₁ Pi.× t₃)
A[BC]-B[AC] = assocl⋆ ◎ (swap⋆ ⊗ id⟷₁) ◎ assocr⋆

A[BC]-B[CA] : {t₁ t₂ t₃ : Pi.U} → t₁ Pi.× (t₂ Pi.× t₃) Pi.⟷₁ t₂ Pi.× (t₃ Pi.× t₁)
A[BC]-B[CA] = swap⋆ ◎ assocr⋆

B[CA]-A[BC] : {t₁ t₂ t₃ : Pi.U} → t₂ Pi.× (t₃ Pi.× t₁) Pi.⟷₁ t₁ Pi.× (t₂ Pi.× t₃)
B[CA]-A[BC] = assocl⋆ ◎ swap⋆
\end{code}

\newcommand{\adder}{%
\begin{code}
C[BA]-[CA]B : C × (B × A) ⟷₁ (C × A) × B
C[BA]-[CA]B = (id⟷₁ ⊗ swap⋆) ◎ assocl⋆
\end{code}}
\begin{code}[hide]
[CA]B-A[BC] : {A B C : U} → (C × A) × B ⟷₁ A × (B × C)
[CA]B-A[BC] = !⟷₁ C[BA]-[CA]B ◎ !⟷₁ A[BC]-C[BA]
\end{code}
\newcommand{\addertwo}{%
\begin{code}
reversibleOr1 : 𝔹 3 ⟷₁ 𝔹 3
reversibleOr1 = A[BC]-C[BA] ◎ ccx ◎ (id⟷₁ ⊗ cx) ◎ C[BA]-[CA]B ◎ (cx ⊗ id⟷₁) ◎ [CA]B-A[BC]
\end{code}}

\newcommand{\resettwo}{%
\begin{code}
reversibleOr2 : 𝔹 3 ⟷₁ 𝔹 3
reversibleOr2 = A[BC]-B[CA] ◎ cif (x ⊗ id⟷₁) cx ◎ B[CA]-A[BC]
\end{code}}


\newcommand{\rotate}{%
\begin{code}
swaplr1 swaplr2 : {A B C : U} → A + (B + C) ⟷₁ C + (B + A)
swaplr1 = assocl₊ ◎ swap₊ ◎ (id⟷₁ ⊕ swap₊)
swaplr2 = (id⟷₁ ⊕ swap₊) ◎ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊ ◎ (id⟷₁ ⊕ swap₊)
\end{code}}

\begin{code}[hide]
open import Pi+.Indexed.Equiv1NormHelpers
step1 = pi^2list (eval₁ (swaplr1 {I} {I} {I}))
\end{code}

\newcommand{\orequiv}{%
\begin{code}
orEquiv : reversibleOr1 ⟷₂ reversibleOr2
orEquiv = TODO
\end{code}}

\begin{code}[hide]
postulate
\end{code}
\newcommand{\combtwo}{%
\begin{code}
  idr◎l       : {c : A ⟷₁ B} → (c ◎ id⟷₁) ⟷₂ c
  swapl₊⟷₂  : {c₁ : A ⟷₁ B} {c₂ : C ⟷₁ D} → (swap₊ ◎ (c₁ ⊕ c₂)) ⟷₂ ((c₂ ⊕ c₁) ◎ swap₊)
\end{code}}
