{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

module Pi.Examples.Presentation where

open import HoTT hiding (_<_ ; ltS ; ltSR ; _+_ ; _×_ ; _++_) public
import lib.types.Nat as N
import lib.types.Sigma as S

open import Pi.UFin.BAut
open import Pi.UFin.UFin as UFin
open import Pi.Common.Misc
open import Pi.Common.Extra

open import Pi.Syntax.Pi+.Indexed as Pi+
open import Pi.Syntax.Pi^ as Pi^
open import Pi.Syntax.Pi^Helpers as Pi^
open import Pi.Syntax.Pi as Pi
open import Pi.Equiv.Translation2
import Pi.Equiv.Equiv1 as Pi+
import Pi.Equiv.Equiv0Hat as Pi^
import Pi.Equiv.Equiv1Hat as Pi^
import Pi.Equiv.Equiv0Norm as Pi^
import Pi.Equiv.Equiv1Norm as Pi^
open import Pi.Equiv.Equiv2
open import Pi.UFin.UFin
open import Pi.UFin.Monoidal
open import Pi.Common.FinHelpers
open import Pi.Lehmer.FinExcept

variable
  m n o p q r : ℕ

-- module a where

--     A B C : Pi+.U 1
--     A = I
--     B = I
--     C = I

--     t1 t2 : A + (B + C) Pi+.⟷₁ C + (B + A)
--     t1 = assocl₊ ◎ swap₊ ◎ (id⟷₁ ⊕ swap₊)
--     t2 = (id⟷₁ ⊕ swap₊) ◎ assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊ ◎ (id⟷₁ ⊕ swap₊)

--     t12 : t1 Pi+.⟷₂ t2
--     t12 = let e1 = Pi+.eval₁ t1
--               e2 = Pi+.eval₁ t2
--               q1 = Pi^.quoteNorm₁ idp e1
--               q2 = Pi^.quoteNorm₁ idp e2
--               p = quote₂ {3} {I + I + I} {I + I + I} {e1} {e2} (e= λ { (0 , _) → idp ; (1 , _) → idp ; (2 , _) → idp ; (S (S (S n)) , p) → {!!} })
--               r1 = Pi+.quote-eval₁ t1
--               r2 = Pi+.quote-eval₁ t2
--           in {!   !}  ■ (p ■ {!  Pi+.quote-eval₁ ? !})

module c where

  xx = (((id⟷₁ ⊕ uniti₊l) ◎ assocl₊) ◎
        (swap₊ ◎ unite₊l) ⊕
        ((id⟷₁ ⊕ uniti₊l) ◎ assocl₊) ◎ (swap₊ ◎ unite₊l) ⊕ id⟷₁)
  yy = ((uniti₊l ◎ swap₊) ⊕
        ((uniti₊l ◎ swap₊) ⊕ id⟷₁) ◎ assocr₊ ◎ id⟷₁ ⊕ unite₊l)
       ◎ assocr₊ ◎ id⟷₁ ⊕ unite₊l

  x : (t : (I + I + O) Pi+.⟷₁ (I + I + O)) → (Pi^.denorm {2} {2} t) Pi+.⟷₂ t
  x id⟷₁ = assoc◎l ■ ((idr◎l ⊡ id⟷₂) ■ linv◎l)
  x (t ◎ t₁) = {!!}
  x (t ⊕ t₁) = {!!}

module b where

    A B : Pi+.U 1
    A = I
    B = I

    t1 t2 : A + (B + O) Pi+.⟷₁ A + (B + O)
    t1 = assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊
    t2 = id⟷₁

    y = Pi^.denorm {2} {2} t2 Pi+.⟷₂ t2
    x : y
    x = assoc◎l ■ ((idr◎l ⊡ id⟷₂) ■ linv◎l)

    z : t1 Pi+.⟷₂ Pi^.denorm t1
    z = Pi+.!⟷₂ (c.x t1)

    qq = (! (+-assoc 1 1 0) ∙
       ap2 N._+_ (+-comm 1 1) idp ∙
       ap2 N._+_ (+-comm 1 1) idp ∙ +-assoc 1 1 0)

    rr : qq == idp
    rr = loop-η qq

    -- postulate
    --   loop-rewrite :  ↦ idp
    --   {-# REWRITE loop-rewrite #-}

    t12 : t1 Pi+.⟷₂ t2
    t12 =
          let e1 = Pi+.eval₁ t1
              e2 = Pi+.eval₁ t2
              -- q1 = Pi^.quoteNorm₁ idp e1
              -- q2 = Pi^.quoteNorm₁ idp e2

              p : _
              p = quote₂ {2} {I + I + O} {I + I + O} {e1} {e2} (e= λ { (0 , _) → idp ; (1 , _) → idp ; (2 , _) → idp ; (S (S (S n)) , p) → {!!} })

              -- x : I + I + O Pi+.⟷₁ I + I + O
              -- x = Pi+.quote₁ idp (Pi+.eval₁ t2)
              -- y : I + I + O Pi+.⟷₁ I + I + O
              -- y = Pi^.denorm t2

              -- p : Pi+.quote₁ idp e1 Pi+.⟷₂ x
              -- p = quote₂ {2} {I + I + O} {I + I + O} {e1} {e2} (e= λ { (0 , _) → idp ; (1 , _) → idp ; (2 , _) → idp ; (S (S (S n)) , p) → {!!} })
              -- r1 : (Pi+.quote₁ (+-comm 1 1 ∙ +-comm 1 1) (Pi+.eval₁ t1)) Pi+.⟷₂ (Pi^.denorm t1)
              -- r1 = Pi+.quote-eval₁ t1
              -- r2 : (Pi+.quote₁ idp (Pi+.eval₁ t2)) Pi+.⟷₂ (Pi^.denorm t2)
              -- r2 = Pi+.quote-eval₁ t2

              y = Pi^.denorm {2} {2} t2 Pi+.⟷₂ t2
              x : y
              x = assoc◎l ■ ((idr◎l ⊡ id⟷₂) ■ linv◎l)

              tt : Pi+.quote₁ idp (Pi+.eval₁ t1) Pi+.⟷₂  Pi+.quote₁ idp e1
              tt = id⟷₂

              ttq : Pi+.quote₁ qq (Pi+.eval₁ t1) Pi+.⟷₂ Pi+.quote₁ idp e1
              ttq = transport (λ p → Pi+.quote₁ p (Pi+.eval₁ t1) Pi+.⟷₂ Pi+.quote₁ idp e1) (! rr) tt

          in (z ■ (Pi+.!⟷₂ (Pi+.quote-eval₁ t1) ■ ttq))  ■ (p ■ (Pi+.quote-eval₁ t2 ■ x))

    -- x : I + I + O Pi+.⟷₁ I + I + O
    -- x = Pi+.quote₁ idp (Pi+.eval₁ t2)
    -- y : I + I + O Pi+.⟷₁ I + I + O
    -- y = Pi^.denorm t2
    -- z : x Pi+.⟷₂ y
    -- z = {!!}

-- r2 : Pi+.quote₁ idp (Pi+.eval₁ t2) Pi+.⟷₂ Pi^.denorm t2
-- r2 = Pi+.quote-eval₁ t2
-- r1 : Pi+.quote₁ (+-comm 1 1 ∙ +-comm 1 1) (Pi+.eval₁ t1) Pi+.⟷₂
--      Pi^.denorm t1
-- r1 = Pi+.quote-eval₁ t1
