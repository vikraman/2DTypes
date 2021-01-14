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

    Fin≃Lehmer :  (Fin n ≃ Fin n) ≃ Lehmer n
    Fin≃Lehmer = TODO

module _ {n : ℕ} where

    immersion-Fin : Lehmer n -> List (Fin n)
    immersion-Fin code = <– List≃LList (immersion code , immersion->> code)

    everything-to-Lehmer : (m : List (Fin n)) -> Σ (Lehmer n) (λ cl -> m ≈[ n ] immersion-Fin cl)
    everything-to-Lehmer m = 
        let r , rp = –> List≃LList m
        in  {!   !}
    
    immersion-is-injection : (cl1 cl2 : Lehmer n) -> ((immersion-Fin cl1) ≈[ n ] (immersion-Fin cl2)) -> cl1 == cl2
    immersion-is-injection cl1 cl2 = {!   !}

    f :  Lehmer n → Sn n
    f = q[_] ∘ immersion-Fin

    g-q :  List (Fin n) → Lehmer n
    g-q m = everything-to-Lehmer m .fst

    g-rel :  {m1 m2 : List (Fin n)} → m1 ≈[ n ] m2 → g-q m1 == g-q m2
    g-rel {m1} {m2} pm = 
        let (cl1 , cl1p) = everything-to-Lehmer m1
            (cl2 , cl2p) = everything-to-Lehmer m2
            p = CoxeterRel-trans (CoxeterRel-sym cl1p) (CoxeterRel-trans pm cl2p)
        in immersion-is-injection cl1 cl2 p
            
    g :  Sn n → Lehmer n
    g = SetQuot-rec {B = Lehmer n} g-q g-rel

    f-g-q : (m : List (Fin n)) → f (g q[ m ]) == q[ m ]
    f-g-q m = quot-rel (CoxeterRel-sym (everything-to-Lehmer m .snd))

    f-g :  (l : Sn n) → f (g l) == l
    f-g = SetQuot-elim {P = λ l → f (g l) == l} {{raise-level -1 has-level-apply-instance}} f-g-q (λ _ →   prop-has-all-paths-↓ {{has-level-apply-instance}})
    -- TODO: why don't the instances resolve?

    g-f :  (w : Lehmer n) → g (f w) == w
    g-f = {!   !}

    Lehmer≃Coxeter :  Lehmer n ≃ Sn n
    Lehmer≃Coxeter = equiv f g f-g g-f
