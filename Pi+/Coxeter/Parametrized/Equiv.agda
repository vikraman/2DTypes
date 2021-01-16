{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module Pi+.Coxeter.Parametrized.Equiv where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.Equivalence
open import lib.PathGroupoid
open import lib.types.Fin
open import lib.types.List

open import Pi+.Coxeter.Common.Lehmer
open import Pi+.Coxeter.Common.ListFinLListEquiv
open import Pi+.Coxeter.Common.LList
open import Pi+.Coxeter.Common.ListN
open import Pi+.Coxeter.NonParametrized.ReductionRel
open import Pi+.Coxeter.NonParametrized.MCoxeter
open import Pi+.Coxeter.NonParametrized.LehmerCanonical using (only-one-canonical↔)
open import Pi+.Coxeter.NonParametrized.LehmerReduction using (Listℕ-to-Lehmer)
open import Pi+.Coxeter.Parametrized.Group
open import Pi+.Coxeter.Parametrized.Coxeter
open import Pi+.Coxeter.Parametrized.ReductionRel
open import Pi+.Coxeter.Parametrized.CoxeterMCoxeterEquiv
open import Pi+.Coxeter.Parametrized.MCoxeter
open import Pi+.Extra

module _ {n : ℕ} where

    Fin≃Lehmer :  (Fin (S n) ≃ Fin (S n)) ≃ Lehmer (S n)
    Fin≃Lehmer = TODO

module _ {n : ℕ} where

    immersionFin : Lehmer (S n) -> List (Fin (S n))
    immersionFin code = <– List≃LList (immersion code , immersion->> code)

    ListFin-to-Lehmer : (m : List (Fin (S n))) -> Σ (Lehmer (S n)) (λ cl -> m ≈₁ immersionFin cl)
    ListFin-to-Lehmer m = 
        let r , rp = –> List≃LList (reverse m)
            np , cl , cl-p = Listℕ-to-Lehmer r
            n>>cl = reduction-implies->> (LList-rev (r , rp)) (immersion cl) cl-p
            cln , cln-p = >>-drop cl (S n) n>>cl
            n>>cln = transport (λ e -> S n >> e) (! cln-p) n>>cl
            cln-f = ((immersion cln) , n>>cln)

            lemma : rev r ≅* immersion cln
            lemma = transport (λ e -> (rev r) ≅* e) (! cln-p) cl-p
            
            reduction : <– List≃LList (LList-rev (r , rp)) ≅*[ n ] <– List≃LList cln-f
            reduction = reduction-fromLList* (LList-rev (r , rp)) cln-f lemma
            
            reduction-t : m ≅*[ n ] <– List≃LList cln-f
            reduction-t = transport (λ e -> e ≅*[ n ] (<– List≃LList cln-f)) (ap fromLList (rev-reverse m) ∙ fromLList∘toLList m) reduction
            
            idp-t : immersionFin cln ≅*[ n ] (<– List≃LList cln-f)
            idp-t = transport (λ e -> e ≅*[ n ] (<– List≃LList cln-f)) (ap fromLList (LList-eq idp)) idpN
        in  cln , mcoxeter->coxeter _ _ (MC reduction-t idp-t)
    
    immersionFin-is-injection : (cl1 cl2 : Lehmer (S n)) -> ((immersionFin cl1) ≈₁ (immersionFin cl2)) -> cl1 == cl2
    immersionFin-is-injection cl1 cl2 p with coxeter->mcoxeter p
    ... | (MC {_} {_} {lf} p1 p2) = 
        let c1 = reduction-toLList* _ _ p1
            c2 = reduction-toLList* _ _ p2
            c1t = transport (λ e -> e ≅* _) (ap fst (toLList∘fromLList _)) c1
            c2t = transport (λ e -> e ≅* _) (ap fst (toLList∘fromLList _)) c2
        in  only-one-canonical↔ cl1 cl2 _ _ idp idp (MC c1t c2t)

    f :  Lehmer (S n) → Sn n
    f = q[_] ∘ immersionFin

    g-q :  List (Fin (S n)) → Lehmer (S n)
    g-q m = ListFin-to-Lehmer m .fst

    g-rel :  {m1 m2 : List (Fin (S n))} → m1 ≈₁ m2 → g-q m1 == g-q m2
    g-rel {m1} {m2} pm = 
        let (cl1 , cl1p) = ListFin-to-Lehmer m1
            (cl2 , cl2p) = ListFin-to-Lehmer m2
            p = CoxeterRel-trans (CoxeterRel-sym cl1p) (CoxeterRel-trans pm cl2p)
        in immersionFin-is-injection cl1 cl2 p
            
    g :  Sn n → Lehmer (S n)
    g = SetQuot-rec {B = Lehmer (S n)} g-q g-rel

    f-g-q : (m : List (Fin (S n))) → f (g q[ m ]) == q[ m ]
    f-g-q m = quot-rel (CoxeterRel-sym (ListFin-to-Lehmer m .snd))

    f-g :  (l : Sn n) → f (g l) == l
    f-g = SetQuot-elim {P = λ l → f (g l) == l} {{raise-level -1 has-level-apply-instance}} f-g-q (λ _ → prop-has-all-paths-↓ {{has-level-apply-instance}})
    -- TODO: why don't the instances resolve?

    g-f :  (cl : Lehmer (S n)) → g (f cl) == cl
    g-f cl =   
        let cln , cln-p = ListFin-to-Lehmer (<– List≃LList (immersion cl , immersion->> cl))
        in  immersionFin-is-injection cln cl (comm cln-p)

    Lehmer≃Coxeter :  Lehmer (S n) ≃ Sn n
    Lehmer≃Coxeter = equiv f g f-g g-f
