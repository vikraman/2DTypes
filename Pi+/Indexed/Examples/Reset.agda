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

module Pi+.Indexed.Examples.Reset where

open import Pi+.Indexed.Examples.Base
open import Pi+.Indexed.Examples.Toffoli

rearrange : (t₁ t₂ t₃ : Pi.U) → t₁ Pi.× (t₂ Pi.× t₃) Pi.⟷₁ t₂ Pi.× (t₁ Pi.× t₃)
rearrange t₁ t₂ t₃ = assocl⋆ ◎ (swap⋆ ⊗ id⟷₁) ◎ assocr⋆

reset : ∀ n → 𝟚 Pi.× 𝔹 n Pi.⟷₁ 𝟚 Pi.× 𝔹 n
reset O = id⟷₁
reset (S O) = swap⋆ ◎ cnot ◎ swap⋆
reset (S (S n)) = rearrange 𝟚 𝟚 (𝔹 (S n)) ◎ cif (not ⊗ id⟷₁) (reset (S n)) ◎ rearrange 𝟚 𝟚 (𝔹 (S n))

reset^ : ∀ n → _
reset^ = eval₁ ∘ reset

reset+ : ∀ n → _
reset+ = Pi^.quote^₁ ∘ Pi^.quoteNorm₁ idp ∘ Pi^.evalNorm₁ ∘ reset^

reset+test : Fin 8 → Fin 8
reset+test = –> (Pi+.eval₁ (reset+ 2))

reset-test : Fin 8 → Fin 8
reset-test = –> (Pi^.evalNorm₁ (eval₁ (reset 2)))

reset2-perm : Aut (Fin 8)
reset2-perm = equiv f f f-f f-f
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

reset2-perm+ : _
reset2-perm+ = (Pi^.quote^₁ ∘ Pi^.quoteNorm₁ idp) reset2-perm

-- ((true , true , true) , false , true , true) ::
-- ((true , true , false) , false , true , false) ::
-- ((true , false , true) , false , false , true) ::
-- ((true , false , false) , true , false , false) ::
-- ((false , true , true) , true , true , true) ::
-- ((false , true , false) , true , true , false) ::
-- ((false , false , true) , true , false , true) ::
-- ((false , false , false) , false , false , false) :: nil

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

-- _ : (reset+test 0 == 0) S.×
--     (reset+test 1 == 1) S.×
--     (reset+test 2 == 2) S.×
--     (reset+test 3 == 3) S.×
--     (reset+test 4 == 4) S.×
--     (reset+test 5 == 5) S.×
--     (reset+test 6 == 6) S.×
--     (reset+test 7 == 7)

-- _ = fin= idp ,
--     fin= idp ,
--     fin= idp ,
--     fin= idp ,
--     fin= idp ,
--     fin= idp ,
--     fin= idp ,
--     fin= idp

{-

(id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
(id⟷₁ ⊕
 id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊)
◎
(id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ id⟷₁ ⊕ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊) ◎
id⟷₁

-}

open import Pi+.Indexed.Examples.Interp

test-interp-reset2 = interp-elems (reset 2)

{-
((true , true , true) , false , true , true) ::
((true , true , false) , false , true , false) ::
((true , false , true) , false , false , true) ::
((true , false , false) , true , false , false) ::
((false , true , true) , true , true , true) ::
((false , true , false) , true , true , false) ::
((false , false , true) , true , false , true) ::
((false , false , false) , false , false , false) :: nil
-}

test-interp-reset2x+ = interp+-elems (Pi^.quote^₁ (eval₁ (reset 2)))

private
  x : _
  x = map encode-interp-elems test-interp-reset2

-- (true , inr (inr (inr (inr true)))) ::
-- (inr true , inr (inr (inr (inr (inr true))))) ::
-- (inr (inr true) , inr (inr (inr (inr (inr (inr true)))))) ::
-- (inr (inr (inr true)) , inr (inr (inr true))) ::
-- (inr (inr (inr (inr true))) , true) ::
-- (inr (inr (inr (inr (inr true)))) , inr true) ::
-- (inr (inr (inr (inr (inr (inr true))))) , inr (inr true)) ::
-- (inr (inr (inr (inr (inr (inr (inr true)))))) ,
--  inr (inr (inr (inr (inr (inr (inr true)))))))
-- :: nil

-- (true , true) ::
-- (inr true , inr true) ::
-- (inr (inr true) , inr (inr true)) ::
-- (inr (inr (inr true)) , inr (inr (inr true))) ::
-- (inr (inr (inr (inr true))) ,
--  inr (inr (inr (inr (inr (inr true))))))
-- ::
-- (inr (inr (inr (inr (inr true)))) ,
--  inr (inr (inr (inr (inr true)))))
-- ::
-- (inr (inr (inr (inr (inr (inr true))))) ,
--  inr (inr (inr (inr true))))
-- ::
-- (inr (inr (inr (inr (inr (inr (inr true)))))) ,
--  inr (inr (inr (inr (inr (inr (inr true)))))))
-- :: nil

test-interp-reset2+ = interp+-elems (reset+ 2)

-- (true , true) ::
-- (inr true , inr true) ::
-- (inr (inr true) , inr (inr true)) ::
-- (inr (inr (inr true)) , inr (inr (inr true))) ::
-- (inr (inr (inr (inr true))) ,
--  inr (inr (inr (inr (inr (inr true))))))
-- ::
-- (inr (inr (inr (inr (inr true)))) ,
--  inr (inr (inr (inr (inr true)))))
-- ::
-- (inr (inr (inr (inr (inr (inr true))))) ,
--  inr (inr (inr (inr true))))
-- ::
-- (inr (inr (inr (inr (inr (inr (inr true)))))) ,
--  inr (inr (inr (inr (inr (inr (inr true)))))))
-- :: nil

test-interp-reset^2 = interp^-elems (reset^ 2)

-- (true , true) ::
-- (inr true , inr true) ::
-- (inr (inr true) , inr (inr true)) ::
-- (inr (inr (inr true)) , inr (inr (inr true))) ::
-- (inr (inr (inr (inr true))) ,
--  inr (inr (inr (inr (inr (inr true))))))
-- ::
-- (inr (inr (inr (inr (inr true)))) ,
--  inr (inr (inr (inr (inr true)))))
-- ::
-- (inr (inr (inr (inr (inr (inr true))))) ,
--  inr (inr (inr (inr true))))
-- ::
-- (inr (inr (inr (inr (inr (inr (inr true)))))) ,
--  inr (inr (inr (inr (inr (inr (inr true)))))))
-- :: nil

open import Pi+.Indexed.Equiv1NormHelpers
open import Pi+.Coxeter.LehmerCoxeterEquiv
open import Pi+.Lehmer.LehmerFinEquiv
reset^-list = pi^2list (reset^ 2)
reset^-list+ = immersion (–> Fin≃Lehmer reset2-perm)
