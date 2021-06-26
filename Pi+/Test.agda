{-# OPTIONS --without-K --rewriting #-}

module Pi+.Test where

open import HoTT

open import Pi+.Lehmer.Lehmer
open import Pi+.Lehmer.LehmerFinEquiv
open import Pi+.Extra
open import Pi+.UFin
open import Pi+.Common.Arithmetic
open import Pi+.Common.ListN
open import Pi+.Coxeter.NonParametrized.LehmerReduction
open import Pi+.Coxeter.LehmerCoxeterEquiv


-- l : List (Fin 3)
-- l = (2 , ltS) :: (1 , ltSR ltS) :: (2 , ltS) :: (1 , ltSR ltS) :: (2 , ltS) :: (1 , ltSR ltS) :: (2 , ltS) :: nil

-- --  5 ∷ 4 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 6 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 6 ∷ 5 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 6 ∷ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ 4 ∷ 3 ∷ 5 ∷ 6 ∷ 4 ∷ 2 ∷ 0 ∷ 0 ∷ 6 ∷ 2 ∷ 6 ∷ 2 ∷ 6 ∷ 6 ∷ 5 ∷ 6 ∷ 4 ∷ 5 ∷ 6 ∷ 6 ∷ 5 ∷ 6 ∷ 4 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 6 ∷ 5 ∷ 4 ∷ 6 ∷ 5 ∷ 3 ∷ 2 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 6 ∷ 5 ∷ 4 ∷ 3 ∷ 6 ∷ 5 ∷ 4 ∷ 2 ∷ 1 ∷ 0 ∷

-- ll : _
-- ll = <– Fin≃Lehmer (immersion⁻¹ l)


-- x0 = –>  ll (0 , ltSR (ltSR (ltSR ltS)))
-- x1 = –> ll (1 , ltSR (ltSR ltS))
-- x2 = –> ll (2 , ltSR ltS)
-- x3 = –> ll (3 , ltS)


-- l : List (Fin 5)
-- l = reverse ((0 , ltSR (ltSR (ltSR (ltSR ltS)))) ::
--     (3 , ltSR ltS) ::
--     (4 , ltS) ::
--     (1 , ltSR (ltSR (ltSR ltS))) ::
--     (3 , ltSR ltS) ::
--     (3 , ltSR ltS) ::
--     (3 , ltSR ltS) :: 
--     nil)

-- --  5 ∷ 4 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 6 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 6 ∷ 5 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 6 ∷ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ 4 ∷ 3 ∷ 5 ∷ 6 ∷ 4 ∷ 2 ∷ 0 ∷ 0 ∷ 6 ∷ 2 ∷ 6 ∷ 2 ∷ 6 ∷ 6 ∷ 5 ∷ 6 ∷ 4 ∷ 5 ∷ 6 ∷ 6 ∷ 5 ∷ 6 ∷ 4 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 6 ∷ 5 ∷ 4 ∷ 6 ∷ 5 ∷ 3 ∷ 2 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 6 ∷ 5 ∷ 4 ∷ 3 ∷ 6 ∷ 5 ∷ 4 ∷ 2 ∷ 1 ∷ 0 ∷

-- ll : _
-- ll = <– Fin≃Lehmer (immersion⁻¹ l)

-- x0 = –> ll (0 , ltSR (ltSR (ltSR (ltSR (ltSR ltS)))))
-- x1 = –> ll (1 , ltSR (ltSR (ltSR (ltSR ltS))))
-- x2 = –> ll (2 , ltSR (ltSR (ltSR ltS)))
-- x3 = –> ll (3 , ltSR (ltSR ltS))
-- x4 = –> ll (4 , ltSR ltS)
-- x5 = –> ll (5 , ltS)

-- lx : List (Fin 6)
-- lx = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: nil

l : List (Fin 7)
l = (6 , ltS) ::
    (6 , ltS) ::
    (5 , ltSR ltS) ::
    (6 , ltS) ::
    (4 , ltSR (ltSR ltS)) ::
    (5 , ltSR ltS) ::
    (6 , ltS) ::
    (6 , ltS) ::
    (5 , ltSR ltS) ::
    (6 , ltS) ::
    (4 , ltSR (ltSR ltS)) ::
    (4 , ltSR (ltSR ltS)) ::
    (6 , ltS) ::
    (6 , ltS) ::
    (5 , ltSR ltS) ::
    (6 , ltS) ::
    (4 , ltSR (ltSR ltS)) ::
    (5 , ltSR ltS) ::
    (6 , ltS) ::
    (6 , ltS) ::
    (5 , ltSR ltS) ::
    (6 , ltS) :: 
    (4 , ltSR (ltSR ltS)) :: 
    nil 

ll1 : _
ll1 = <– Fin≃Lehmer (immersion⁻¹ l)

x0 = –> ll1 (0 , ltSR (ltSR (ltSR (ltSR (ltSR (ltSR (ltSR ltS)))))))
x1 = –> ll1 (1 , ltSR (ltSR (ltSR (ltSR (ltSR (ltSR ltS))))))
x2 = –> ll1 (2 , ltSR (ltSR (ltSR (ltSR (ltSR ltS)))))
x3 = –> ll1 (3 , ltSR (ltSR (ltSR (ltSR ltS))))
x4 = –> ll1 (4 , ltSR (ltSR (ltSR ltS)))
x5 = –> ll1 (5 , ltSR (ltSR ltS))
x6 = –> ll1 (6 , ltSR ltS)
x7 = –> ll1 (7 , ltS)

lx : List (Fin 8)
lx = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: nil

ll2 : _
ll2 = <– Fin≃Lehmer (immersion⁻¹ (reverse l))

y0 = –> ll2 (0 , ltSR (ltSR (ltSR (ltSR (ltSR (ltSR (ltSR ltS)))))))
y1 = –> ll2 (1 , ltSR (ltSR (ltSR (ltSR (ltSR (ltSR ltS))))))
y2 = –> ll2 (2 , ltSR (ltSR (ltSR (ltSR (ltSR ltS)))))
y3 = –> ll2 (3 , ltSR (ltSR (ltSR (ltSR ltS))))
y4 = –> ll2 (4 , ltSR (ltSR (ltSR ltS)))
y5 = –> ll2 (5 , ltSR (ltSR ltS))
y6 = –> ll2 (6 , ltSR ltS)
y7 = –> ll2 (7 , ltS)

ly : List (Fin 8)
ly = y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: y7 :: nil
