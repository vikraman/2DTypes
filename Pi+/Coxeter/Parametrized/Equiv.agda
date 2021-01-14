{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Parametrized.Equiv where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.Equivalence
open import lib.types.Fin
open import lib.types.List

open import Pi+.Coxeter.Common.Lehmer using (Lehmer; immersion; immersion->>)
open import Pi+.Coxeter.Common.ListFinLListEquiv
open import Pi+.Coxeter.Parametrized.Group
open import Pi+.Coxeter.Parametrized.Coxeter
open import Pi+.Coxeter.NonParametrized.LehmerCanonical using (only-one-canonical↔)
open import Pi+.Extra

module _ {n : ℕ} where

    Fin≃Lehmer :  (Fin (S n) ≃ Fin (S n)) ≃ Lehmer (S n)
    Fin≃Lehmer = TODO

module _ {n : ℕ} where

    immersion-Fin : Lehmer (S n) -> List (Fin (S n))
    immersion-Fin code = <– List≃LList (immersion code , immersion->> code)

    everything-to-Lehmer : (m : List (Fin (S n))) -> Σ (Lehmer (S n)) (λ cl -> m ≈₁ immersion-Fin cl)
    everything-to-Lehmer m = 
        let r , rp = –> List≃LList m
        in  {!   !}
    
    immersion-is-injection : (cl1 cl2 : Lehmer (S n)) -> ((immersion-Fin cl1) ≈₁ (immersion-Fin cl2)) -> cl1 == cl2
    immersion-is-injection cl1 cl2 = {!   !}

    f :  Lehmer (S n) → Sn n
    f = q[_] ∘ immersion-Fin

    g-q :  List (Fin (S n)) → Lehmer (S n)
    g-q m = everything-to-Lehmer m .fst

    g-rel :  {m1 m2 : List (Fin (S n))} → m1 ≈₁ m2 → g-q m1 == g-q m2
    g-rel {m1} {m2} pm = 
        let (cl1 , cl1p) = everything-to-Lehmer m1
            (cl2 , cl2p) = everything-to-Lehmer m2
            p = CoxeterRel-trans (CoxeterRel-sym cl1p) (CoxeterRel-trans pm cl2p)
        in immersion-is-injection cl1 cl2 p
            
    g :  Sn n → Lehmer (S n)
    g = SetQuot-rec {B = Lehmer (S n)} g-q g-rel

    f-g-q : (m : List (Fin (S n))) → f (g q[ m ]) == q[ m ]
    f-g-q m = quot-rel (CoxeterRel-sym (everything-to-Lehmer m .snd))

    f-g :  (l : Sn n) → f (g l) == l
    f-g = SetQuot-elim {P = λ l → f (g l) == l} {{raise-level -1 has-level-apply-instance}} f-g-q (λ _ →   prop-has-all-paths-↓ {{has-level-apply-instance}})
    -- TODO: why don't the instances resolve?

    g-f :  (w : Lehmer (S n)) → g (f w) == w
    g-f = {!   !}

    Lehmer≃Coxeter :  Lehmer (S n) ≃ Sn n
    Lehmer≃Coxeter = equiv f g f-g g-f
