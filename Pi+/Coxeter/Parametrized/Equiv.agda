{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.Parametrized.Equiv where

open import lib.Base
open import lib.NType
open import lib.NType2
open import lib.Equivalence
open import lib.PathGroupoid
open import lib.types.Fin
open import lib.types.List

open import Pi+.Coxeter.Common.Lehmer renaming (immersion to immersionLehmer)
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
open import Pi+.Misc

immersion : {n : ℕ} -> Lehmer n -> List (Fin n)
immersion {O} CanZ = nil
immersion {S n} code = <– List≃LList (immersionLehmer code , immersion->> code)

ListFin-to-Lehmer : {n : ℕ} -> (m : List (Fin (S n))) -> Σ (Lehmer (S n)) (λ cl -> m ≈₁ immersion cl)
ListFin-to-Lehmer {n} m = 
    let r , rp = –> List≃LList (reverse m)
        np , cl , cl-p = Listℕ-to-Lehmer r
        n>>cl = reduction-implies->> (LList-rev (r , rp)) (immersionLehmer cl) cl-p
        cln , cln-p = >>-drop cl (S n) n>>cl
        n>>cln = transport (λ e -> S n >> e) (! cln-p) n>>cl
        cln-f = ((immersionLehmer cln) , n>>cln)

        lemma : rev r ≅* immersionLehmer cln
        lemma = transport (λ e -> (rev r) ≅* e) (! cln-p) cl-p
        
        reduction : <– List≃LList (LList-rev (r , rp)) ≅*[ n ] <– List≃LList cln-f
        reduction = reduction-fromLList* (LList-rev (r , rp)) cln-f lemma
        
        reduction-t : m ≅*[ n ] <– List≃LList cln-f
        reduction-t = transport (λ e -> e ≅*[ n ] (<– List≃LList cln-f)) (ap fromLList (rev-reverse m) ∙ fromLList∘toLList m) reduction
        
        idp-t : immersion cln ≅*[ n ] (<– List≃LList cln-f)
        idp-t = transport (λ e -> e ≅*[ n ] (<– List≃LList cln-f)) (ap fromLList (LList-eq idp)) idpN
    in  cln , mcoxeter->coxeter _ _ (MC reduction-t idp-t)

immersion-is-injection : {n : ℕ} -> (cl1 cl2 : Lehmer (S n)) -> ((immersion cl1) ≈₁ (immersion cl2)) -> cl1 == cl2
immersion-is-injection cl1 cl2 p with coxeter->mcoxeter p
... | (MC {_} {_} {lf} p1 p2) = 
    let c1 = reduction-toLList* _ _ p1
        c2 = reduction-toLList* _ _ p2
        c1t = transport (λ e -> e ≅* _) (ap fst (toLList∘fromLList _)) c1
        c2t = transport (λ e -> e ≅* _) (ap fst (toLList∘fromLList _)) c2
    in  only-one-canonical↔ cl1 cl2 _ _ idp idp (MC c1t c2t)

immersion⁻¹ : {n : ℕ} ->  List (Fin n) → Lehmer n
immersion⁻¹ {O} nil = CanZ
immersion⁻¹ {S n} m = ListFin-to-Lehmer m .fst

immersion⁻¹-respects≈ :  {n : ℕ} ->  {m1 m2 : List (Fin n)} → m1 ≈ m2 → immersion⁻¹ m1 == immersion⁻¹ m2
immersion⁻¹-respects≈ {O} {nil} {nil} pm = idp
immersion⁻¹-respects≈ {S n} {m1} {m2} pm = 
    let (cl1 , cl1p) = ListFin-to-Lehmer m1
        (cl2 , cl2p) = ListFin-to-Lehmer m2
        p = CoxeterRel-trans {S n} (CoxeterRel-sym {S n} cl1p) (CoxeterRel-trans {S n} pm cl2p)
    in immersion-is-injection cl1 cl2 p

immersion∘immersion⁻¹ : {n : ℕ} -> (m : List (Fin n)) → immersion (immersion⁻¹ m) ≈ m
immersion∘immersion⁻¹ {O} nil = unit
immersion∘immersion⁻¹ {S n} m = CoxeterRel-sym {S n} (ListFin-to-Lehmer m .snd)

immersion⁻¹∘immersion : {n : ℕ} ->  (cl : Lehmer n) → immersion⁻¹ (immersion cl) == cl
immersion⁻¹∘immersion {O} CanZ = idp
immersion⁻¹∘immersion {S n} cl =   
    let cln , cln-p = ListFin-to-Lehmer (<– List≃LList (immersionLehmer cl , immersion->> cl))
    in  immersion-is-injection cln cl (comm cln-p)


module _ {n : ℕ} where

    Fin≃Lehmer :  Aut (Fin (S n)) ≃ Lehmer n
    Fin≃Lehmer = TODO

module _ {n : ℕ} where

    UFin≃Lehmer : Ω (UFin , FinFS (S n)) ≃ Lehmer n
    UFin≃Lehmer = TODO -- Fin≃Lehmer ∘e UFin≃Fin