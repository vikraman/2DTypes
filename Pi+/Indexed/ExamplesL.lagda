\begin{code}[hide]
module Pi+.Indexed.ExamplesL where

open import Pi+.Indexed.SyntaxFull as Pi
open import Pi+.Indexed.Syntax as Pi+
open import Pi+.Indexed.Examples.Base
open import Pi+.Indexed.Examples.Reset
\end{code}

\newcommand{\resettwo}{%
\begin{code}
reset2 : 𝟚 Pi.× 𝔹 2 Pi.⟷₁ 𝟚 Pi.× 𝔹 2
reset2 =  (assocl⋆ ◎ (swap⋆ ⊗ id⟷₁) ◎ assocr⋆) ◎
          (dist  ◎ ((id⟷₁ ⊗ (swap₊ ⊗ id⟷₁)) ⊕
                    (id⟷₁ ⊗ (swap⋆ ◎ (dist ◎ ((id⟷₁ ⊗ swap₊) ⊕ id⟷₁) ◎ factor) ◎ swap⋆)))
                 ◎ factor) ◎
          assocl⋆ ◎ (swap⋆ ⊗ id⟷₁) ◎ assocr⋆
\end{code}}

\newcommand{\resetnormtwo}{%
\begin{code}
reset2Norm : 𝟠+ Pi+.⟷₁ 𝟠+
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
