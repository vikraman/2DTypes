\begin{code}[hide]
{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}
module Pi+.Indexed.ExamplesL where

open import HoTT hiding (_<_ ; ltS ; ltSR ; _+_ ; _×_)
import lib.types.Nat as N
import lib.types.Sigma as S

open import Pi+.UFin.BAut
open import Pi+.Misc
open import Pi+.Extra

open import Pi+.Indexed.Syntax as Pi+ renaming (_⟷₁_ to _⟷₁₊_; U to U+)
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
open import Pi+.Indexed.Examples.Toffoli
open import Pi+.Indexed.Examples.Reset hiding (reset; reset2-perm)
\end{code}

\newcommand{\resettwo}{%
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
\end{code}

\newcommand{\adder}{%
\begin{code}
adder3 : 𝔹 3 Pi.⟷₁ 𝔹 3
adder3 =  swap⋆ ◎ (swap⋆ ⊗ id⟷₁) ◎ assocr⋆ ◎
          toffoli 3 ◎ (id⟷₁ ⊗ cnot) ◎
          assocl⋆ ◎ (swap⋆ ⊗ id⟷₁) ◎ assocr⋆ ◎
          (id⟷₁ ⊗ cnot) ◎ assocl⋆ ◎ swap⋆
\end{code}}

\newcommand{\rotate}{%
\begin{code}
swaplr1 swaplr2 : {A B C : U} → A + (B + C) ⟷₁ C + (B + A)
swaplr1 = assocl₊ ◎ swap₊ ◎ (id⟷₁ ⊕ swap₊)
swaplr2 = (id⟷₁ ⊕ swap₊) ◎ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊ ◎ (id⟷₁ ⊕ swap₊)
\end{code}}
