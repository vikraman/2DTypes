{-# OPTIONS --without-K --rewriting #-}

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
open import Pi+.UFin

immersionFin : {n : ℕ} -> Lehmer n -> List (Fin n)
immersionFin {O} CanZ = nil
immersionFin {S n} code = <– List≃LList (immersion code , immersion->> code)

ListFin-to-Lehmer : {n : ℕ} -> (m : List (Fin (S n))) -> Σ (Lehmer (S n)) (λ cl -> m ≈₁ immersionFin cl)
ListFin-to-Lehmer {n} m = 
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

immersionFin-is-injection : {n : ℕ} -> (cl1 cl2 : Lehmer (S n)) -> ((immersionFin cl1) ≈₁ (immersionFin cl2)) -> cl1 == cl2
immersionFin-is-injection cl1 cl2 p with coxeter->mcoxeter p
... | (MC {_} {_} {lf} p1 p2) = 
    let c1 = reduction-toLList* _ _ p1
        c2 = reduction-toLList* _ _ p2
        c1t = transport (λ e -> e ≅* _) (ap fst (toLList∘fromLList _)) c1
        c2t = transport (λ e -> e ≅* _) (ap fst (toLList∘fromLList _)) c2
    in  only-one-canonical↔ cl1 cl2 _ _ idp idp (MC c1t c2t)

Lehmer≃Sn : {n : ℕ} ->  Lehmer n ≃ Sn n
Lehmer≃Sn = equiv f g f-g g-f
    where
        f : {n : ℕ} -> Lehmer n → Sn n
        f = q[_] ∘ immersionFin

        g-q : {n : ℕ} ->  List (Fin n) → Lehmer n
        g-q {O} nil = CanZ
        g-q {S n} m = ListFin-to-Lehmer m .fst

        g-rel :  {n : ℕ} ->  {m1 m2 : List (Fin n)} → m1 ≈ m2 → g-q m1 == g-q m2
        g-rel {O} {nil} {nil} pm = idp
        g-rel {S n} {m1} {m2} pm = 
            let (cl1 , cl1p) = ListFin-to-Lehmer m1
                (cl2 , cl2p) = ListFin-to-Lehmer m2
                p = CoxeterRel-trans {S n} (CoxeterRel-sym {S n} cl1p) (CoxeterRel-trans {S n} pm cl2p)
            in immersionFin-is-injection cl1 cl2 p
                
        g :  {n : ℕ} -> Sn n → Lehmer n
        g {n} = SetQuot-rec {B = Lehmer n} g-q g-rel

        f-g-q : {n : ℕ} -> (m : List (Fin n)) → f (g q[ m ]) == q[ m ]
        f-g-q {O} nil = idp
        f-g-q {S n} m = quot-rel (CoxeterRel-sym {S n} (ListFin-to-Lehmer m .snd))

        f-g :  {n : ℕ} -> (l : Sn n) → f (g l) == l
        f-g = SetQuot-elim {P = λ l → f (g l) == l} {{raise-level -1 has-level-apply-instance}} f-g-q (λ _ → prop-has-all-paths-↓ {{has-level-apply-instance}})
        -- TODO: why don't the instances resolve?

        g-f : {n : ℕ} ->  (cl : Lehmer n) → g (f cl) == cl
        g-f {O} CanZ = idp
        g-f {S n} cl =   
            let cln , cln-p = ListFin-to-Lehmer (<– List≃LList (immersion cl , immersion->> cl))
            in  immersionFin-is-injection cln cl (comm cln-p)


Aut : ∀ {ℓ} → Type ℓ → Type ℓ
Aut T = T ≃ T

Ω : ∀ {ℓ} → Σ (Type ℓ) (λ X → X) → Type ℓ
Ω (X , x) = (x == x)

module _ {n : ℕ} where

    UFin≃Fin : Ω (UFin , FinFS n) ≃ Aut (Fin n)
    UFin≃Fin = TODO

module _ {n : ℕ} where

    Fin≃Lehmer :  Aut (Fin (S n)) ≃ Lehmer n
    Fin≃Lehmer = TODO

module _ {n : ℕ} where

    UFin≃Sn : Ω (UFin , FinFS (S n)) ≃ Sn n
    UFin≃Sn = TODO -- composition of the above