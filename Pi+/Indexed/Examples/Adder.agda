{-# OPTIONS --overlapping-instances #-}

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

module Pi+.Indexed.Examples.Adder where

open import Pi+.Indexed.Examples.Base
open import Pi+.Indexed.Examples.Toffoli

{--

Write another circuit that does this addition:

0 -> 0
8 -> 8
n -> n + 8 `mod` 16

use algorithm in \cite{10.1145/775832.775915}

when we normalize we should get the same as reset+
        f1    f2      f3      f4         f5     f6         f7          f8
            cx(3,0) cx(2,0) ccx(2,3,0) cx(1,0) ccx(1,3,0) ccx(1,2,0) cccx(1,2,3,0)
0000 - 0000  0000    0000    0000       0000   0000       0000        0000
0001 - 1001  0001    0001    0001       0001   0001       0001        0001
0010 - 1010  1010    0010    0010       0010   0010       0010        0010
0011 - 1011  0011    1011    0011       0011   0011       0011        0011
0100 - 1100  1100    1100    1100       0100   0100       0100        0100
0101 - 1101  0101    0101    0101       1101   0101       0101        0101
0110 - 1110  1110    0110    0110       1110   1110       0110        0110
0111 - 1111  0111    1111    0111       1111   0111       1111        0111
1000 - 1000  1000    1000    1000       1000   1000       1000        1000
1001 - 0001  1001    1001    1001       1001   1001       1001        1001
1010 - 0010  0010    1010    1010       1010   1010       1010        1010
1011 - 0011  1011    0011    1011       1011   1011       1011        1011
1100 - 0100  0100    0100    0100       1100   1100       1100        1100
1101 - 0101  1101    1101    1101       0101   1101       1101        1101
1110 - 0110  0110    1110    1110       0110   0110       1110        1110
1111 - 0111  1111    0111    1111       0111   1111       0111        1111

circuit:

  cccx(1,2,3,0);
  ccx(1,2,0);
  ccx(1,3,0);
  cx(1,0);
  ccx(2,3,0);
  cx(2,0);
  cx(3,0)

check

0000
0001
0010 1010
0011 1011 0011 1011
0100 1100
0101 1101 0101 1101
0110 1110 0110 1110
0111 1111 0111 1111 0111 1111 0111 1111
1000
1001 0001
1010 0010
1011 0011 1011 0011
1100 0100
1101 0101 1101 0101
1110 0110 1110 0110
1111 0111 1111 0111 1111 0111 1111 0111

--}

-- adder4 : 𝔹 4 Pi.⟷₁ 𝔹 4
-- adder4 = -- 0 x (1 x (2 x 3))
--   swap⋆ ◎ -- (1 x (2 x 3)) x 0
--   assocr⋆ ◎ -- 1 x ((2 x 3) x 0)
--   (id⟷₁ ⊗ assocr⋆) ◎ -- 1 x (2 x (3 x 0))
--   toffoli 4 ◎ -- 1 x (2 x (3 x 0))
--   (id⟷₁ ⊗ (id⟷₁ ⊗ swap⋆)) ◎ -- 1 x (2 x (0 x 3)
--   (id⟷₁ ⊗ assocl⋆) ◎ -- 1 x ((2 x 0) x 3)
--   assocl⋆ ◎ -- (1 x (2 x 0)) x 3
--   (toffoli 3 ⊗ id⟷₁) ◎ -- (1 x (2 x 0)) x 3
--   assocr⋆ ◎ -- 1 x ((2 x 0) x 3)
--   (id⟷₁ ⊗ swap⋆) ◎ -- 1 x (3 x (2 x 0))
--   (id⟷₁ ⊗ (id⟷₁ ⊗ swap⋆)) ◎ -- 1 x (3 x (0 x 2))
--   (id⟷₁ ⊗ assocl⋆) ◎ -- 1 x ((3 x 0) x 2)
--   assocl⋆ ◎ -- (1 x (3 x 0)) x 2
--   (toffoli 3 ⊗ id⟷₁) ◎ -- (1 x (3 x 0)) x 2
--   ((id⟷₁ ⊗ swap⋆) ⊗ id⟷₁) ◎ -- (1 x (0 x 3)) x 2
--   (assocl⋆ ⊗ id⟷₁) ◎ -- ((1 x 0) x 3) x 2
--   ((cnot ⊗ id⟷₁) ⊗ id⟷₁) ◎ -- ((1 x 0) x 3) x 2
--   assocr⋆ ◎ -- (1 x 0) x (3 x 2)
--   (swap⋆ ⊗ id⟷₁) ◎ -- (0 x 1) x (3 x 2)
--   swap⋆ ◎ -- (3 x 2) x (0 x 1)
--   assocl⋆ ◎ -- ((3 x 2) x 0) x 1
--   (assocr⋆ ⊗ id⟷₁) ◎ -- (3 x (2 x 0)) x 1
--   (toffoli 3 ⊗ id⟷₁) ◎ -- (3 x (2 x 0)) x 1
--   ((id⟷₁ ⊗ cnot) ⊗ id⟷₁) ◎ -- (3 x (2 x 0)) x 1
--   ((id⟷₁ ⊗ swap⋆) ⊗ id⟷₁) ◎ -- (3 x (0 x 2)) x 1
--   (assocl⋆ ⊗ id⟷₁) ◎ -- ((3 x 0) x 2) x 1
--   ((cnot ⊗ id⟷₁) ⊗ id⟷₁) ◎ -- ((3 x 0) x 2) x 1
--   ((swap⋆ ⊗ id⟷₁) ⊗ id⟷₁) ◎ -- ((0 x 3) x 2) x 1
--   (assocr⋆ ⊗ id⟷₁) ◎ -- (0 x (3 x 2)) x 1
--   assocr⋆ ◎ -- 0 x ((3 x 2) x 1)
--   (id⟷₁ ⊗ swap⋆) ◎ -- 0 x (1 x (3 x 2))
--   (id⟷₁ ⊗ (id⟷₁ ⊗ swap⋆)) -- 0 x (1 x (2 x 3))

-- adder4+ : Pi^.quote^₀ 16 Pi+.⟷₁ Pi^.quote^₀ 16
-- adder4+ = (Pi^.quote^₁ ∘ Pi^.quoteNorm₁ idp ∘ Pi^.evalNorm₁ ∘ eval₁) adder4

-- adder4+test : Fin 16 → Fin 16
-- -- adder4+test = –> (Pi+.eval₁ (adder+))
-- adder4+test = –> (Pi^.evalNorm₁ (eval₁ adder4))

adder31 : 𝔹 3 Pi.⟷₁ 𝔹 3
adder31 = -- 0 * (1 * 2)
  swap⋆ ◎ -- (1 * 2) * 0
  (swap⋆ ⊗ id⟷₁) ◎ -- (2 * 1) * 0
  assocr⋆ -- 2 * (1 * 0)

adder32 : 𝔹 3 Pi.⟷₁ 𝔹 3
adder32 =
  toffoli 3 ◎ -- 2 * (1 * 0)
  (id⟷₁ ⊗ cnot) -- 2 * (1 * 0)

adder33 : 𝔹 3 Pi.⟷₁ 𝔹 3
adder33 =
  assocl⋆ ◎ -- (2 * 1) * 0
  (swap⋆ ⊗ id⟷₁) ◎ -- (1 * 2) * 0
  assocr⋆ -- 1 * (2 * 0)

adder34 : 𝔹 3 Pi.⟷₁ 𝔹 3
adder34 =
  (id⟷₁ ⊗ cnot) ◎ -- 1 * (2 * 0)
  assocl⋆ ◎ -- (1 * 2) * 0
  swap⋆ -- 0 * (1 * 2)

adder3 : 𝔹 3 Pi.⟷₁ 𝔹 3
adder3 =
  adder31 ◎
  adder32 ◎
  adder33 ◎
  adder34

-- adder3+test : Fin 8 → Fin 8
-- adder4+test = –> (Pi+.eval₁ (adder3+))
-- adder3+test = –> (Pi^.evalNorm₁ (eval₁ adder3))

open import Pi+.Lehmer.Lehmer2
open import Pi+.Indexed.Equiv1NormHelpers
open import Pi+.Coxeter.Lehmer2CoxeterEquiv

fastadder3+test : Lehmer 7
fastadder3+test = (Pi^.fastevalNorm₁ (eval₁ adder3))

fastadder3+test2 = eval₁ adder3

fastadder3+test3 = (pi^2list fastadder3+test2)

fastadder3+test4 = immersion⁻¹ fastadder3+test3

adderPerm : Aut (Fin 8)
adderPerm = equiv f f f-f f-f
  where f : Fin 8 → Fin 8
        f (O , ϕ) = 0
        f (1 , ϕ) = 5
        f (2 , ϕ) = 6
        f (3 , ϕ) = 7
        f (4 , ϕ) = 4
        f (5 , ϕ) = 1
        f (6 , ϕ) = 2
        f (7 , ϕ) = 3
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

adderPerm^ : 8 Pi^.⟷₁^ 8
adderPerm^ = Pi^.quoteNorm₁ idp adderPerm

adderPerm+ : 𝟠+ Pi+.⟷₁ 𝟠+
adderPerm+ = Pi^.quote^₁ adderPerm^

fastadder+test231 = eval₁ adder31

fastadder+test331 = (pi^2list fastadder+test231)

fastadder+test431 = immersion⁻¹ fastadder+test331

fastadder+test31 = Pi^.fastevalNorm₁ (eval₁ adder31)
slowadder+test31 = Pi^.evalNorm₁ (eval₁ adder31)

fastadder+test32 = Pi^.fastevalNorm₁ (eval₁ adder32)
slowadder+test32 = Pi^.evalNorm₁ (eval₁ adder32)

fastadder+test33 = Pi^.fastevalNorm₁ (eval₁ adder33)
slowadder+test33 = Pi^.evalNorm₁ (eval₁ adder33)

fastadder+test34 = Pi^.fastevalNorm₁ (eval₁ adder34)
slowadder+test34 = Pi^.evalNorm₁ (eval₁ adder34)

adder+test34-perm : Aut (Fin 8)
adder+test34-perm =
  slowadder+test34 ∘e slowadder+test33 ∘e slowadder+test32 ∘e slowadder+test31
  -- compose in reverse order

adder+test34+ : Pi^.quote^₀ 8 Pi+.⟷₁ Pi^.quote^₀ 8
adder+test34+ = (Pi^.quote^₁ ∘ Pi^.quoteNorm₁ idp) adder+test34-perm

adder+test34+-full : Pi^.quote^₀ 8 Pi+.⟷₁ Pi^.quote^₀ 8
adder+test34+-full = (Pi^.quote^₁ ∘ Pi^.quoteNorm₁ idp ∘ Pi^.evalNorm₁ ∘ eval₁) adder3

{-
adder3:

(assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
(id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
(id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
(id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
(id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
(id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
(assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ id⟷₁
-}

{-
reset2:

(assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
(id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
(assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎ id⟷₁

-}
