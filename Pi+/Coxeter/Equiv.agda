{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Equiv where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.Equivalence
open import lib.types.Fin

open import Pi+.Coxeter.Lehmer using (Lehmer)
open import Pi+.Extra

module _ {n : ℕ} where

    Fin≃Lehmer :  (Fin n ≃ Fin n) ≃ Lehmer n
    Fin≃Lehmer = TODO

open import Pi+.Coxeter.Group

module _ {n : ℕ} where

    immersion : Lehmer n -> ListN n
    immersion = TODO

    postulate
        everything-to-Lehmer : (m : ListN n) -> Σ (Lehmer n) (λ cl -> m ≈[ n ] immersion cl)
        immersion-is-injection : (cl1 cl2 : Lehmer n) -> ((immersion cl1) ≈[ n ] (immersion cl2)) -> cl1 == cl2

    f :  Lehmer n → Sn n
    f = q[_] ∘ immersion

    g-q :  ListN n → Lehmer n
    g-q m = everything-to-Lehmer m .fst

    g-rel :  {m1 m2 : ListN n} → m1 ≈[ n ] m2 → g-q m1 == g-q m2
    g-rel {m1} {m2} pm = 
        let (cl1 , cl1p) = everything-to-Lehmer m1
            (cl2 , cl2p) = everything-to-Lehmer m2
            p = CoxeterRel-trans (CoxeterRel-sym cl1p) (CoxeterRel-trans pm cl2p)
        in immersion-is-injection cl1 cl2 p
            
    g :  Sn n → Lehmer n
    g = SetQuot-rec {B = Lehmer n} g-q g-rel

    f-g-q : (m : ListN n) → f (g q[ m ]) == q[ m ]
    f-g-q m = quot-rel (CoxeterRel-sym (everything-to-Lehmer m .snd))

    f-g :  (l : Sn n) → f (g l) == l
    f-g = SetQuot-elim {P = λ l → f (g l) == l} {{raise-level -1 has-level-apply-instance}} f-g-q (λ _ →   prop-has-all-paths-↓ {{has-level-apply-instance}})
    -- TODO: why don't the instances resolve?

    g-f :  (w : Lehmer n) → g (f w) == w
    g-f = TODO

    Lehmer≃Coxeter :  Lehmer n ≃ Sn n
    Lehmer≃Coxeter = equiv f g f-g g-f