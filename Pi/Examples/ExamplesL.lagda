\begin{code}[hide]
{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}
module Pi.Examples.ExamplesL where

open import HoTT hiding (_<_ ; ltS ; ltSR ; _+_ ; _×_)
import lib.types.Nat as N
import lib.types.Sigma as S

open import Pi.UFin.BAut
open import Pi.Common.Misc
open import Pi.Common.Extra

open import Pi.Syntax.Pi+.Indexed as Pi+
  renaming (_⟷₁_ to _⟷₁₊_; _⟷₂_ to _⟷₂₊_; !⟷₁ to !⟷₁₊; U to U+;
  idr◎l to idr◎l+; swapl₊⟷₂ to swapl₊⟷₂+; unite₊r to unite₊r+)
open import Pi.Syntax.Pi^ as Pi^
open import Pi.Syntax.Pi^Helpers as Pi^
open import Pi.Syntax.Pi as Pi hiding (_⟷₂_)
open import Pi.Equiv.Translation2
import Pi.Equiv.Equiv1 as Pi+
import Pi.Equiv.Equiv0Hat as Pi^
import Pi.Equiv.Equiv1Hat as Pi^
import Pi.Equiv.Equiv0Norm as Pi^
import Pi.Equiv.Equiv1Norm as Pi^
open import Pi.UFin.UFin
open import Pi.UFin.Monoidal
open import Pi.Common.FinHelpers
open import Pi.Lehmer.FinExcept

open import Pi.Examples.Base
open import Pi.Examples.Toffoli hiding (cif ; toffoli₄)
open import Pi.Examples.Reset hiding (reset; reset2-perm)

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

\newcommand{\extendedToffoli}{%
\begin{code}
toffoli₃¹ toffoli₃² toffoli₃³ toffoli₃⁴ : 𝔹 4 ⟷₁ 𝔹 4
toffoli₃¹ = cif (cif (swap₊ ⊗ id⟷₁) (id⟷₁ ⊗ id⟷₁)) (id⟷₁ ⊗ (id⟷₁ ⊗ id⟷₁))
toffoli₃² = cif (cif (id⟷₁ ⊗ swap₊) (id⟷₁ ⊗ id⟷₁)) (id⟷₁ ⊗ (id⟷₁ ⊗ id⟷₁))
toffoli₃³ = cif (cif (id⟷₁ ⊗ id⟷₁) (swap₊ ⊗ id⟷₁)) (id⟷₁ ⊗ (id⟷₁ ⊗ id⟷₁))
toffoli₃⁴ = cif (cif (id⟷₁ ⊗ id⟷₁) (id⟷₁ ⊗ swap₊)) (id⟷₁ ⊗ (id⟷₁ ⊗ id⟷₁))
\end{code}}

\newcommand{\toffoli}{%
\begin{code}
toffoli₄ : 𝔹 4 ⟷₁ 𝔹 4
toffoli₄ = controlled (controlled (controlled not))
\end{code}}

\newcommand{\resetnormtwo}{%
\begin{code}
reversibleOrNorm : 𝟠+ ⟷₁₊ 𝟠+
reversibleOrNorm =  (id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
                    (id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
                    (assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
                    -- elided
\end{code}}
\begin{code}[hide]
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
\end{code}
\newcommand{\resetperm}{%
\begin{code}
reversibleOrPerm : Aut (Fin 8)
reversibleOrPerm = equiv f f f-f f-f
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
open import Pi.Equiv.Equiv1NormHelpers
step1 = pi^2list (eval₁ (swaplr1 {I} {I} {I}))
\end{code}

\newcommand{\orequiv}{%
\begin{code}
--orEquiv : reversibleOr1 ⟷₂ reversibleOr2
--orEquiv = TODO
\end{code}}

\begin{code}[hide]
data _⟷₂_ : {X : U} {Y : U} → X ⟷₁ Y → X ⟷₁ Y → Set where
\end{code}

\newcommand{\leveltwoblockone}{%
\begin{code}
  assoc◎l   : {c₁ : A ⟷₁ B} {c₂ : B ⟷₁ C} {c₃ : C ⟷₁ D} → (c₁ ◎ (c₂ ◎ c₃)) ⟷₂ ((c₁ ◎ c₂) ◎ c₃)
  assoc◎r   : {c₁ : A ⟷₁ B} {c₂ : B ⟷₁ C} {c₃ : C ⟷₁ D} → ((c₁ ◎ c₂) ◎ c₃) ⟷₂ (c₁ ◎ (c₂ ◎ c₃))
  assocl₊l  : {c₁ : A ⟷₁ B} {c₂ : C ⟷₁ D} {c₃ : E ⟷₁ F} → ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊) ⟷₂ (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃))
  assocl₊r  : {c₁ : A ⟷₁ B} {c₂ : C ⟷₁ D} {c₃ : E ⟷₁ F} → (assocl₊ ◎ ((c₁ ⊕ c₂) ⊕ c₃)) ⟷₂ ((c₁ ⊕ (c₂ ⊕ c₃)) ◎ assocl₊)
  assocr₊r  : {c₁ : A ⟷₁ B} {c₂ : C ⟷₁ D} {c₃ : E ⟷₁ F} → (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊) ⟷₂ (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃)))
  assocr₊l  : {c₁ : A ⟷₁ B} {c₂ : C ⟷₁ D} {c₃ : E ⟷₁ F} → (assocr₊ ◎ (c₁ ⊕ (c₂ ⊕ c₃))) ⟷₂ (((c₁ ⊕ c₂) ⊕ c₃) ◎ assocr₊)
\end{code}}

\newcommand{\leveltwoblocktwo}{%
\begin{code}
  idl◎l   : {c : A ⟷₁ B} → (id⟷₁ ◎ c) ⟷₂ c
  idl◎r   : {c : A ⟷₁ B} → c ⟷₂ id⟷₁ ◎ c
  idr◎l   : {c : A ⟷₁ B} → (c ◎ id⟷₁) ⟷₂ c
  idr◎r   : {c : A ⟷₁ B} → c ⟷₂ (c ◎ id⟷₁)

  linv◎l  : {c : A ⟷₁ B} → (c ◎ !⟷₁ c) ⟷₂ id⟷₁
  linv◎r  : {c : A ⟷₁ B} → id⟷₁ ⟷₂ (c ◎ !⟷₁ c)
  rinv◎l  : {c : A ⟷₁ B} → (!⟷₁ c ◎ c) ⟷₂ id⟷₁
  rinv◎r  : {c : A ⟷₁ B} → id⟷₁ ⟷₂ (!⟷₁ c ◎ c)

  unite₊l⟷₂l  : {c₁ : O ⟷₁ O} {c₂ : A ⟷₁ B} → (unite₊l ◎ c₂) ⟷₂ ((c₁ ⊕ c₂) ◎ unite₊l)
  unite₊l⟷₂r  : {c₁ : O ⟷₁ O} {c₂ : A ⟷₁ B} → ((c₁ ⊕ c₂) ◎ unite₊l) ⟷₂ (unite₊l ◎ c₂)
  uniti₊l⟷₂l  : {c₁ : O ⟷₁ O} {c₂ : A ⟷₁ B} → (uniti₊l ◎ (c₁ ⊕ c₂)) ⟷₂ (c₂ ◎ uniti₊l)
  uniti₊l⟷₂r  : {c₁ : O ⟷₁ O} {c₂ : A ⟷₁ B} → (c₂ ◎ uniti₊l) ⟷₂ (uniti₊l ◎ (c₁ ⊕ c₂))
  swapl₊⟷₂    : {c₁ : A ⟷₁ B} {c₂ : C ⟷₁ D} → (swap₊ ◎ (c₁ ⊕ c₂)) ⟷₂ ((c₂ ⊕ c₁) ◎ swap₊)
  swapr₊⟷₂    : {c₁ : A ⟷₁ B} {c₂ : C ⟷₁ D} → ((c₂ ⊕ c₁) ◎ swap₊) ⟷₂ (swap₊ ◎ (c₁ ⊕ c₂))

  id⟷₂     : {c : A ⟷₁ B} → c ⟷₂ c
  _■_      : {c₁ c₂ c₃ : A ⟷₁ B} → (c₁ ⟷₂ c₂) → (c₂ ⟷₂ c₃) → (c₁ ⟷₂ c₃)
  _⊡_      : {c₁ : A ⟷₁ B} {c₂ : B ⟷₁ C} {c₃ : A ⟷₁ B} {c₄ : B ⟷₁ C} → (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ◎ c₂) ⟷₂ (c₃ ◎ c₄)
  resp⊕⟷₂  : {c₁ : A ⟷₁ B} {c₂ : C ⟷₁ D} {c₃ : A ⟷₁ B} {c₄ : C ⟷₁ D} → (c₁ ⟷₂ c₃) → (c₂ ⟷₂ c₄) → (c₁ ⊕ c₂) ⟷₂ (c₃ ⊕ c₄)

  id⟷₁⊕id⟷₁⟷₂  : (id⟷₁ {A} ⊕ id⟷₁ {B}) ⟷₂ id⟷₁
  split⊕-id⟷₁  : (id⟷₁ {A + B}) ⟷₂ (id⟷₁ ⊕ id⟷₁)
  hom⊕◎⟷₂      : {c₁ : E ⟷₁ A} {c₂ : F ⟷₁ B} {c₃ : A ⟷₁ C} {c₄ : B ⟷₁ D} → ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⟷₂ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
  hom◎⊕⟷₂      : {c₁ : E ⟷₁ A} {c₂ : F ⟷₁ B} {c₃ : A ⟷₁ C} {c₄ : B ⟷₁ D} → ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄)) ⟷₂ ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄))

  triangle₊l  : (unite₊r {A} ⊕ id⟷₁ {B}) ⟷₂ assocr₊ ◎ (id⟷₁ ⊕ unite₊l)
  triangle₊r  : assocr₊ ◎ (id⟷₁ {A} ⊕ unite₊l {B}) ⟷₂ unite₊r ⊕ id⟷₁
  pentagon₊l  : assocr₊ ◎ (assocr₊ {A} {B} {C + D}) ⟷₂ ((assocr₊ ⊕ id⟷₁) ◎ assocr₊) ◎ (id⟷₁ ⊕ assocr₊)
  pentagon₊r  : ((assocr₊ {A} {B} {C} ⊕ id⟷₁ {D}) ◎ assocr₊) ◎ (id⟷₁ ⊕ assocr₊) ⟷₂ assocr₊ ◎ assocr₊

  unite₊l-coh-l  : unite₊l {A} ⟷₂ swap₊ ◎ unite₊r
  unite₊l-coh-r  : swap₊ ◎ unite₊r ⟷₂ unite₊l {A}
  hexagonr₊l     : (assocr₊ ◎ swap₊) ◎ assocr₊ {A} {B} {C} ⟷₂ ((swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ (id⟷₁ ⊕ swap₊)
  hexagonr₊r     : ((swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ (id⟷₁ ⊕ swap₊) ⟷₂ (assocr₊ ◎ swap₊) ◎ assocr₊ {A} {B} {C}
  hexagonl₊l     : (assocl₊ ◎ swap₊) ◎ assocl₊ {A} {B} {C} ⟷₂ ((id⟷₁ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷₁)
  hexagonl₊r     : ((id⟷₁ ⊕ swap₊) ◎ assocl₊) ◎ (swap₊ ⊕ id⟷₁) ⟷₂ (assocl₊ ◎ swap₊) ◎ assocl₊ {A} {B} {C}
\end{code}}

\begin{code}[hide]
postulate
\end{code}
\newcommand{\combtwo}{%
\begin{code}
  xidr◎l       : {c : A ⟷₁ B} → (c ◎ id⟷₁) ⟷₂ c
  xswapl₊⟷₂  : {c₁ : A ⟷₁ B} {c₂ : C ⟷₁ D} → (swap₊ ◎ (c₁ ⊕ c₂)) ⟷₂ ((c₂ ⊕ c₁) ◎ swap₊)
\end{code}}
