{-# OPTIONS --without-K --rewriting --termination-depth=2 #-}

module Pi+.Coxeter.Parametrized.ReductionRel where

open import lib.Base
open import lib.Relation
open import lib.Equivalence
open import lib.PathGroupoid
open import lib.NType
open import lib.types.Nat
open import lib.types.SetQuotient public
open import lib.types.List
open import lib.types.Fin

open import Pi+.Misc
open import Pi+.Coxeter.Common.LList
open import Pi+.Coxeter.Common.InequalityEquiv
open import Pi+.Coxeter.Common.ListFinLListEquiv
open import Pi+.Coxeter.Common.ListN renaming (_++_ to _++ℕ_; ++-assoc to ++-assocℕ)
open import Pi+.Coxeter.NonParametrized.ReductionRel


⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
⟨_⟩ = Fin-S

S⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
S⟨ k , kltn ⟩ = S k , <-ap-S kltn

_<^_ : {m : ℕ} -> Fin m -> Fin m -> Type₀
n <^ k = (n .fst) < (k .fst)

syntax DownArrow x y p = x ↓⟨ p ⟩ y

DownArrow : {m : ℕ} -> (n : Fin m) -> (k : Fin m) -> (k <^ n) -> List (Fin (S m))
DownArrow n (O , kp) p = S⟨ n ⟩ :: (⟨ n ⟩ :: nil )
DownArrow {S m} (S n , np) (S k , kp) p =
    let rec = DownArrow {m} (n , <-cancel-S np) (k , <-cancel-S kp) (<-cancel-S p)
    in  S⟨ (S n , np) ⟩ :: map ⟨_⟩ rec


syntax ReductionRel n x y = x ≅[ n ] y

data ReductionRel : (m : ℕ) -> List (Fin (S m)) -> List (Fin (S m)) -> Type₀ where
  cancelN≅ : {m : ℕ} -> (l : List (Fin (S m))) -> (r : List (Fin (S m))) -> (n : Fin (S m)) 
    -> (l ++ (n :: (n :: r))) ≅[ m ] (l ++ r)
  swapN≅ : {m : ℕ} -> (l : List (Fin (S m))) -> (r : List (Fin (S m))) -> (n k : Fin (S m)) -> (S (k .fst) < (n .fst)) 
    -> (l ++ (n :: (k :: r))) ≅[ m ] l ++ (k :: (n :: r))
  longN≅ : {m : ℕ} -> (l : List (Fin (S m))) -> (r : List (Fin (S m))) -> (n k : Fin m) -> (p : k <^ n)
    -> (l ++ (n ↓⟨ p ⟩ k) ++ (S⟨ n ⟩ :: r)) ≅[ m ] (l ++ (⟨ n ⟩ :: (n ↓⟨ p ⟩ k) ++ r))

syntax ReductionRel* n x y = x ≅*[ n ] y

data ReductionRel* : (m : ℕ) -> (l : List (Fin (S m))) -> (r : List (Fin (S m))) -> Type₀ where
  idpN : {m : ℕ} {l : List (Fin (S m))} -> l ≅*[ m ] l
  transN≅ : {m : ℕ} {l1 l2 l3 : List (Fin (S m))} -> (l1 ≅[ m ] l2) -> (l2 ≅*[ m ] l3) -> l1 ≅*[ m ] l3

extN : {m : ℕ} {l1 l2 : List (Fin (S m))} -> (l1 ≅[ m ] l2) -> (l1 ≅*[ m ] l2)
extN p = transN≅ p idpN

reduction-implies->> : {n : ℕ} -> (s : LList n) -> (sf : Listℕ) -> ((s .fst) ≅* sf) -> n >> sf
reduction-implies->> {n} (s , lp) .s idp = lp
reduction-implies->> {n} (s , lp) sf (trans≅ (cancel≅ l r .s mf defm defmf) p) = 
    let Sn>>l++r = transport (λ e -> n >> e) defm lp
        Sn>>l = >>-implies->> {n} {s} {nil} {l} {_ ∷ _ ∷ r} lp defm
        Sn>>r = >>-implies->> {n} {s} {l ++ℕ _ ∷ _ ∷ nil} {r} {nil} lp (defm ∙ ! (++-assocℕ l (_ ∷ _ ∷ nil) r) ∙ ! ++-unit ∙ ++-assocℕ _ r nil)
    in  reduction-implies->> (mf , transport (λ e -> n >> e) (! defmf) (>>-++ Sn>>l Sn>>r)) sf p
reduction-implies->> {n} (s , lp) sf (trans≅ (swap≅ {m} {k} x l r .s mf defm defmf) p) =
    let Sn>>l++m∷k∷r = transport (λ e -> n >> e) defm lp
        Sn>>l = >>-implies->> {n} {s} {nil} {l} {_ ∷ _ ∷ r} lp defm
        Sn>k = >>-implies->  {n} {k} {s} {l ++ℕ [ m ]} {r} lp (defm ∙ ! (++-assocℕ l [ m ] (k ∷ r)))
        Sn>m = >>-implies-> {n} {m} {s} {l} {k ∷ r} lp defm
        Sn>>r = >>-implies->> {n} {s} {l ++ℕ _ ∷ _ ∷ nil} {r} {nil} lp (defm ∙ ! (++-assocℕ l (_ ∷ _ ∷ nil) r) ∙ ! ++-unit ∙ ++-assocℕ _ r nil)
        Sn>>k∷m∷r = k :⟨ Sn>k ⟩: (m :⟨ Sn>m ⟩: Sn>>r)
    in  reduction-implies->> (mf , transport (λ e -> n >> e) (! defmf) (>>-++ Sn>>l Sn>>k∷m∷r)) sf p
reduction-implies->> {n} (s , lp) sf (trans≅ (long≅ k l₁ r .s mf defm defmf) p) = reduction-implies->> {!   !} sf p

reduction-fromLList : {n : ℕ} -> (s sf : LList (S n)) -> (p : (s .fst) ≅ (sf .fst)) -> (<– List≃LList s ≅[ n ] <– List≃LList sf)
reduction-fromLList {n} s sf (cancel≅ {m} l r .(s .fst) .(sf .fst) defm defmf) = 
    let m<n = >>-implies-> (s .snd) defm
        ll = <– List≃LList (l , >>-implies->> {l1 = nil} {m1 = l} {r1 = m ∷ m ∷ r} (s .snd) defm)
        rr = <– List≃LList (r , >>-implies->> {l1 = l ++ℕ m ∷ m ∷ nil} {m1 = r} {r1 = nil} (s .snd) (defm ∙ ! (++-assocℕ l (m ∷ m ∷ nil) r) ∙ (! ++-unit) ∙ ++-assocℕ (l ++ℕ m ∷ m ∷ nil) r nil))
        c = cancelN≅ ll rr (m , <– <N≃< m<n)
        Sn>>l++r = transport (λ e -> S n >> e) defmf (sf .snd)
        eqsf = (fromLList-++ (l , _) (r , _) ∙ ap fromLList (LList-eq {S n} {(l ++ℕ r) , _} {(l ++ℕ r) , Sn>>l++r} idp)) ∙ ap (<– List≃LList) (LList-eq (! defmf))
        Sn>>l++m∷m∷r = transport (λ e -> S n >> e) defm (s .snd)
        eqs = (fromLList-++ (l , _) ((m ∷ m ∷ r) , _) ∙ ap (λ e -> fromLList {S n} e) (LList-eq {S n} {(l ++ℕ m ∷ m ∷ r) , _} {(l ++ℕ m ∷ m ∷ r) , Sn>>l++m∷m∷r} idp))  ∙ ap (<– List≃LList) (LList-eq (! defm))
    in  transport2 (λ e f → ReductionRel n e f) eqs eqsf c
reduction-fromLList {n} s sf (swap≅ {m} {k} x l r .(s .fst) .(sf .fst) defm defmf) = 
    let m<n = >>-implies-> (s .snd) defm
        k<n = >>-implies-> (s .snd) (defm ∙ ! (++-assocℕ l [ m ] (k ∷ r)))
        ll = <– List≃LList (l , >>-implies->> {l1 = nil} {m1 = l} {r1 = m ∷ k ∷ r} (s .snd) defm)
        rr = <– List≃LList (r , >>-implies->> {l1 = l ++ℕ m ∷ k ∷ nil} {m1 = r} {r1 = nil} (s .snd) (defm ∙ ! (++-assocℕ l (m ∷ k ∷ nil) r) ∙ (! ++-unit) ∙ ++-assocℕ (l ++ℕ m ∷ k ∷ nil) r nil))
        c = swapN≅ ll rr (m , <– <N≃< m<n) (k , <– <N≃< k<n) (<– <N≃< x)
        Sn>>l++k∷m∷r = transport (λ e -> S n >> e) defmf (sf .snd)
        Sn>>l = >>-implies->> {_} {_} {nil} {l} {k ∷ m ∷ r} (sf .snd) defmf
        Sn>>k∷m∷r = >>-implies->> {_} {_} {l} {k ∷ m ∷ r} {nil} (sf .snd) (defmf ∙ ap (λ e -> l ++ℕ k ∷ m ∷ e) (! ++-unit))
        eqsf = fromLList-++ (l , Sn>>l) ((k ∷ m ∷ r) , Sn>>k∷m∷r) ∙ 
               ap fromLList (LList-eq {S n} {(l ++ℕ k ∷ m ∷ r) , _} {(l ++ℕ k ∷ m ∷ r) , Sn>>l++k∷m∷r} idp) ∙ 
               ap (λ e -> <– List≃LList e) (LList-eq {S n} {(l ++ℕ k ∷ m ∷ r) , Sn>>l++k∷m∷r} {sf} (! defmf))
        Sn>>l++m∷k∷r = transport (λ e -> S n >> e) defm (s .snd)
        Sn>>m∷k∷r = >>-implies->> {_} {_} {l} {m ∷ k ∷ r} {nil} (s .snd) (defm ∙ ap (λ e -> l ++ℕ m ∷ k ∷ e) (! ++-unit))
        eqs = fromLList-++ (l , Sn>>l) ((m ∷ k ∷ r) , Sn>>m∷k∷r) ∙ 
              ap (λ e -> fromLList {S n} e) (LList-eq {S n} {(l ++ℕ m ∷ k ∷ r) , _} {(l ++ℕ m ∷ k ∷ r) , Sn>>l++m∷k∷r} idp) ∙ 
              ap (<– List≃LList) (LList-eq {S n} {(l ++ℕ m ∷ k ∷ r) , Sn>>l++m∷k∷r} {s} (! defm))
    in  transport2 (λ e f → ReductionRel n e f) {!  eqs !} {! eqsf  !} c -- 
reduction-fromLList {n} s sf (long≅ k l r .(s .fst) .(sf .fst) defm defmf) = {!   !}

reduction-fromLList* : {n : ℕ} -> (s sf : LList (S n)) -> (p : (s .fst) ≅* (sf .fst)) -> (<– List≃LList s ≅*[ n ] <– List≃LList sf)
reduction-fromLList* {n} (s , sp1) (s , sp2) idp rewrite (>>-eq sp1 sp2) = idpN
reduction-fromLList* {n} s sf (trans≅ {m2 = m2} x p) = 
    let c = reduction-fromLList s (m2 , (reduction-implies->> s m2 (ext x))) x
        rec = reduction-fromLList* {n} _ sf p
    in  transN≅ c rec

-- reduction-toLList : {n : ℕ} -> (m mf : LList n) -> ((m .fst) ≅* (mf .fst)) -> (m ≅*[ n ] mf)
-- reduction-toLList = ?

-- {-# NON_TERMINATING #-}
-- LList-to-LehmerProper : {n : ℕ} -> (m : LList n) -> Σ _ (λ nf -> (n ≤ nf) × Σ _ (λ cl -> rev (m .fst) ≅* immersionProper {nf} cl))
-- LList-to-LehmerProper {n} m = 
--   let rn , rcl = Listℕ-to-LehmerProper (m .fst)
--   in {!   !}
