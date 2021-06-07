{-# OPTIONS --without-K --exact-split --rewriting #-}

open import lib.Base
open import lib.Equivalence
open import lib.NType
import lib.types.Nat as N
open import lib.types.Fin

open import Pi+.UFin.BAut
open import Pi+.Misc
open import Pi+.Extra

module Pi+.Indexed.ExpMod where

open import Pi+.Indexed.Syntax as Pi+
open import Pi+.Indexed.SyntaxHat as Pi^
open import Pi+.Indexed.SyntaxHatHelpers as Pi^
open import Pi+.Indexed.SyntaxFull as Pi
open import Pi+.Indexed.Translation
import Pi+.Indexed.Equiv1 as Pi+
import Pi+.Indexed.Equiv1Hat as Pi^
import Pi+.Indexed.Equiv1Norm as Pi^
import Pi+.Indexed.Examples

{--

f(r) = 11^r mod 15

g :: B^2 x B^4 ⟷ B^2 x B^4
g(r,h) = (r , h ⊕ f(r))

g(r,h) where r even and h even = (r , h+1)
g(r,h) where r even and h odd = (r , h-1)
g(r,0) where r odd = (r,11)
g(r,1) where r odd = (r,10)
g(r,2) where r odd = (r,9)
g(r,3) where r odd = (r,8)
g(r,4) where r odd = (r,15)
g(r,5) where r odd = (r,14)
g(r,6) where r odd = (r,13)
g(r,7) where r odd = (r,12)
g(r,8) where r odd = (r,3)
g(r,9) where r odd = (r,2)
g(r,10) where r odd = (r,1)
g(r,11) where r odd = (r,0)
g(r,12) where r odd = (r,7)
g(r,13) where r odd = (r,6)
g(r,14) where r odd = (r,5)
g(r,15) where r odd = (r,4)

0000 => 1011
0001 => 1010
0010 => 1001
0011 => 1000
0100 => 1111
0101 => 1110
0110 => 1101
0111 => 1100
1000 => 0011
1001 => 0010
1010 => 0001
1011 => 0000
1100 => 0111
1101 => 0110
1110 => 0101
1111 => 0100


--}

g-perm : Aut (Fin 16)
g-perm = equiv f f f-f f-f
  where f : Fin 16 → Fin 16
        f (O , ϕ) = 11 , N.ltSR (N.ltSR (N.ltSR (N.ltSR N.ltS)))
        f (1 , ϕ) = 10 , N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR N.ltS))))
        f (2 , ϕ) = 9 , N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR N.ltS)))))
        f (3 , ϕ) = 8 , N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR N.ltS))))))
        f (4 , ϕ) = 15 , N.ltS
        f (5 , ϕ) = 14 , N.ltSR N.ltS
        f (6 , ϕ) = 13 , N.ltSR (N.ltSR N.ltS)
        f (7 , ϕ) = 12 , N.ltSR (N.ltSR (N.ltSR N.ltS))
        f (8 , ϕ) = 3 , N.ltSR
                          (N.ltSR
                           (N.ltSR
                            (N.ltSR
                             (N.ltSR
                              (N.ltSR
                               (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR N.ltS)))))))))))
        f (9 , ϕ) = 2 , N.ltSR
                          (N.ltSR
                           (N.ltSR
                            (N.ltSR
                             (N.ltSR
                              (N.ltSR
                               (N.ltSR
                                (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR N.ltS))))))))))))
        f (10 , ϕ) = 1 , N.ltSR
                           (N.ltSR
                            (N.ltSR
                             (N.ltSR
                              (N.ltSR
                               (N.ltSR
                                (N.ltSR
                                 (N.ltSR
                                  (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR N.ltS)))))))))))))
        f (11 , ϕ) = 0 , N.ltSR
                           (N.ltSR
                            (N.ltSR
                             (N.ltSR
                              (N.ltSR
                               (N.ltSR
                                (N.ltSR
                                 (N.ltSR
                                  (N.ltSR
                                   (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR N.ltS))))))))))))))
        f (12 , ϕ) = 7 , N.ltSR
                           (N.ltSR
                            (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR N.ltS)))))))
        f (13 , ϕ) = 6 , N.ltSR
                           (N.ltSR
                            (N.ltSR
                             (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR N.ltS))))))))
        f (14 , ϕ) = 5 , N.ltSR
                           (N.ltSR
                            (N.ltSR
                             (N.ltSR
                              (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR N.ltS)))))))))
        f (15 , ϕ) = 4 , N.ltSR
                           (N.ltSR
                            (N.ltSR
                             (N.ltSR
                              (N.ltSR
                               (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR N.ltS))))))))))
        f (n , N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR ()))))))))))))))))
        f-f : (x : Fin 16) → f (f x) == x
        f-f (O , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (1 , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (2 , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (3 , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (4 , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (5 , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (6 , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (7 , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (8 , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (9 , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (10 , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (11 , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (12 , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (13 , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (14 , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (15 , ϕ) = pair= idp (prop-has-all-paths _ _)
        f-f (n , N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR (N.ltSR ()))))))))))))))))

g^ : 16 ⟷₁^ 16
g^ = Pi^.quoteNorm₁ idp g-perm

𝟙𝟞+ : Pi+.U 16
𝟙𝟞+ = I + I + I + I + I + I + I + I + I + I + I + I + I + I + I + I + O

g+ : 𝟙𝟞+ Pi+.⟷₁ 𝟙𝟞+
g+ = Pi^.quote^₁ g^
