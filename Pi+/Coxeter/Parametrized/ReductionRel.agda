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
open import Pi+.Extra
open import Pi+.Coxeter.Common.LList
open import Pi+.Coxeter.Common.InequalityEquiv
open import Pi+.Coxeter.Common.ListFinLListEquiv
open import Pi+.Coxeter.Common.ListN renaming (_++_ to _++ℕ_; ++-assoc to ++-assocℕ)
open import Pi+.Coxeter.NonParametrized.ReductionRel
open import Pi+.Coxeter.Common.Arithmetic renaming (_<_ to _<ℕ_; ≤-trans to ≤-transℕ)

⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
⟨_⟩ = Fin-S

S⟨_⟩ : ∀ {n} → Fin n → Fin (S n)
S⟨ k , kltn ⟩ = S k , <-ap-S kltn

_≤^_ : {m : ℕ} -> Fin m -> Fin m -> Type₀
k ≤^ n = (k .fst) < S (n .fst)

syntax DownArrow x y p = x ↓⟨ p ⟩ y

DownArrow : {m : ℕ} -> (n : Fin m) -> (k : Fin m) -> (k ≤^ n) -> List (Fin (S m))
DownArrow n (O , kp) p = S⟨ n ⟩ :: (⟨ n ⟩ :: nil )
DownArrow {S m} (S n , np) (S k , kp) p =
    let rec = DownArrow {m} (n , <-cancel-S np) (k , <-cancel-S kp) (<-cancel-S p)
    in  S⟨ (S n , np) ⟩ :: map ⟨_⟩ rec
DownArrow {S m} (O , snd₁) (S fst₁ , snd₂) (ltSR ())


syntax ReductionRel n x y = x ≅[ n ] y

data ReductionRel : (m : ℕ) -> List (Fin (S m)) -> List (Fin (S m)) -> Type₀ where
  cancelN≅ : {m : ℕ} -> (l : List (Fin (S m))) -> (r : List (Fin (S m))) -> (n : Fin (S m)) 
    -> (l ++ (n :: (n :: r))) ≅[ m ] (l ++ r)
  swapN≅ : {m : ℕ} -> (l : List (Fin (S m))) -> (r : List (Fin (S m))) -> (n k : Fin (S m)) -> (S (k .fst) < (n .fst)) 
    -> (l ++ (n :: (k :: r))) ≅[ m ] l ++ (k :: (n :: r))
  longN≅ : {m : ℕ} -> (l : List (Fin (S m))) -> (r : List (Fin (S m))) -> (n k : Fin m) -> (p : k ≤^ n)
    -> (l ++ (n ↓⟨ p ⟩ k) ++ (S⟨ n ⟩ :: r)) ≅[ m ] (l ++ (⟨ n ⟩ :: (n ↓⟨ p ⟩ k) ++ r))

syntax ReductionRel* n x y = x ≅*[ n ] y

data ReductionRel* : (m : ℕ) -> (l : List (Fin (S m))) -> (r : List (Fin (S m))) -> Type₀ where
  idpN : {m : ℕ} {l : List (Fin (S m))} -> l ≅*[ m ] l
  transN≅ : {m : ℕ} {l1 l2 l3 : List (Fin (S m))} -> (l1 ≅[ m ] l2) -> (l2 ≅*[ m ] l3) -> l1 ≅*[ m ] l3

extN : {m : ℕ} {l1 l2 : List (Fin (S m))} -> (l1 ≅[ m ] l2) -> (l1 ≅*[ m ] l2)
extN p = transN≅ p idpN

transN : {m : ℕ} -> {l1 l2 l3 : List (Fin (S m))} -> (l1 ≅*[ m ] l2) -> (l2 ≅*[ m ] l3) -> l1 ≅*[ m ] l3
transN idpN p  = p
transN (transN≅ x q) p = transN≅ x (transN q p)

reduction-respects-++-l : {m : ℕ} -> {l r r' : List (Fin (S m))} -> (r ≅[ m ] r') -> ((l ++ r) ≅[ m ] (l ++ r'))
reduction-respects-++-l {m} {ll} (cancelN≅ l r n) =
    let c = cancelN≅ (ll ++ l) r n
    in  transport2 (λ e f -> e ≅[ m ] f) (++-assoc ll _ _) (++-assoc ll _ _) c
reduction-respects-++-l {m} {ll} (swapN≅ l r n k x) = 
    let c = swapN≅ (ll ++ l) r n k x
    in  transport2 (λ e f -> e ≅[ m ] f) (++-assoc ll _ _) (++-assoc ll _ _) c
reduction-respects-++-l {m} {ll} (longN≅ l r n k p) =
    let c = longN≅ (ll ++ l) r n k p
    in  transport2 (λ e f -> e ≅[ m ] f) (++-assoc ll _ _) (++-assoc ll _ _) c

reduction-respects-++-r : {m : ℕ} -> {l l' r : List (Fin (S m))} -> (l ≅[ m ] l') -> ((l ++ r) ≅[ m ] (l' ++ r))
reduction-respects-++-r {m} {r = rr} (cancelN≅ l r n) =
    let c = cancelN≅ l (r ++ rr) n
    in  transport2 (λ e f -> e ≅[ m ] f) (! (++-assoc l _ _)) (! (++-assoc l _ _)) c
reduction-respects-++-r {m} {r = rr} (swapN≅ l r n k x) = 
    let c = swapN≅ l (r ++ rr) n k x
    in  transport2 (λ e f -> e ≅[ m ] f) (! (++-assoc l _ _)) (! (++-assoc l _ _)) c
reduction-respects-++-r {m} {r = rr} (longN≅ l r n k p) =
    let c = longN≅ l (r ++ rr) n k p
        p1 = l ++ ((n ↓⟨ p ⟩ k) ++ (S⟨ n ⟩ :: r ++ rr)) =⟨ ap (l ++_) (! (++-assoc (n ↓⟨ p ⟩ k) (S⟨ n ⟩ :: r) _)) ⟩
             l ++ (((n ↓⟨ p ⟩ k) ++ (S⟨ n ⟩ :: r)) ++ rr) =⟨ ! (++-assoc l _ _) ⟩
             (l ++ ((n ↓⟨ p ⟩ k) ++ (S⟨ n ⟩ :: r))) ++ rr =∎
        p2 = l ++ (⟨ n ⟩ :: (n ↓⟨ p ⟩ k) ++ (r ++ rr)) =⟨ ap (l ++_) (! (++-assoc (⟨ n ⟩ :: (n ↓⟨ p ⟩ k)) r _)) ⟩
             l ++ (⟨ n ⟩ :: ((n ↓⟨ p ⟩ k) ++ r) ++ rr) =⟨ ! (++-assoc l _ _) ⟩
             (l ++ (Fin-S n :: (n ↓⟨ p ⟩ k) ++ r)) ++ rr =∎
    in  transport2 (λ e f -> e ≅[ m ] f) p1 p2 c

reduction*-respects-++ : {m : ℕ} -> {l l' r r' : List (Fin (S m))} -> (l ≅*[ m ] l') -> (r ≅*[ m ] r') -> ((l ++ r) ≅*[ m ] (l' ++ r'))
reduction*-respects-++ idpN idpN = idpN
reduction*-respects-++  idpN (transN≅ x pr) = 
    let cr = reduction-respects-++-l x
        rec = reduction*-respects-++ idpN pr
    in  transN≅ cr rec
reduction*-respects-++ (transN≅ x pl) idpN =
    let cl = reduction-respects-++-r x
        rec = reduction*-respects-++ pl idpN
    in  transN≅ cl rec
reduction*-respects-++ (transN≅ xl pl) (transN≅ xr pr) =
    let cl = reduction-respects-++-r xl
        cr = reduction-respects-++-l xr
        rec = reduction*-respects-++ pl pr
    in  transN (transN (extN cl) (extN cr)) rec

reduction-implies->> : {n : ℕ} -> (s : LList n) -> (sf : Listℕ) -> ((s .fst) ≅* sf) -> n >> sf
reduction-implies->> {n} (s , sp) .s idp = sp
reduction-implies->> {n} (s , sp) sf (trans≅ (cancel≅ l r .s mf defm defmf) p) = 
    let Sn>>l++r = transport (λ e -> n >> e) defm sp
        Sn>>l = >>-implies->> {n} {s} {nil} {l} {_ ∷ _ ∷ r} sp defm
        Sn>>r = >>-implies->> {n} {s} {l ++ℕ _ ∷ _ ∷ nil} {r} {nil} sp (defm ∙ ! (++-assocℕ l (_ ∷ _ ∷ nil) r) ∙ ! ++-unit ∙ ++-assocℕ _ r nil)
    in  reduction-implies->> (mf , transport (λ e -> n >> e) (! defmf) (>>-++ Sn>>l Sn>>r)) sf p
reduction-implies->> {n} (s , sp) sf (trans≅ (swap≅ {m} {k} x l r .s mf defm defmf) p) =
    let Sn>>l++m∷k∷r = transport (λ e -> n >> e) defm sp
        Sn>>l = >>-implies->> {n} {s} {nil} {l} {_ ∷ _ ∷ r} sp defm
        Sn>k = >>-implies->  {n} {k} {s} {l ++ℕ [ m ]} {r} sp (defm ∙ ! (++-assocℕ l [ m ] (k ∷ r)))
        Sn>m = >>-implies-> {n} {m} {s} {l} {k ∷ r} sp defm
        Sn>>r = >>-implies->> {n} {s} {l ++ℕ _ ∷ _ ∷ nil} {r} {nil} sp (defm ∙ ! (++-assocℕ l (_ ∷ _ ∷ nil) r) ∙ ! ++-unit ∙ ++-assocℕ _ r nil)
        Sn>>k∷m∷r = k :⟨ Sn>k ⟩: (m :⟨ Sn>m ⟩: Sn>>r)
    in  reduction-implies->> (mf , transport (λ e -> n >> e) (! defmf) (>>-++ Sn>>l Sn>>k∷m∷r)) sf p
reduction-implies->> {n} (s , sp) sf (trans≅ (long≅ {m} k l r .s mf defm defmf) p) = 
    let Sn>>l++↓∷r = transport (λ e -> n >> e) defm sp
        Sn>>l = >>-implies->> {n} {s} {nil} {l} {S (k + m) ∷ k + m ∷ m ↓ k ++ℕ (1 + k + m) ∷ r} sp defm
        Sn>k+m = >>-implies-> {n} {k + m} {s} {l ++ℕ [ S (k + m) ]} {(m ↓ k ++ℕ S (k + m) ∷ r)} sp (defm ∙ ! (++-assocℕ l [ S(k + m) ] _))
        Sn>Sk+m = >>-implies-> {n} {S (k + m)} {_} {l} {k + m ∷ m ↓ k ++ℕ (1 + k + m) ∷ r} Sn>>l++↓∷r idp
        Sn>>r = >>-implies->> {n} {s} {l ++ℕ S (k + m) ∷ k + m ∷ m ↓ k ++ℕ [ 1 + k + m ]} {r} {nil} sp (defm ∙ 
            ! (++-assocℕ l _ (r ++ℕ nil) ∙ ap (λ e -> l ++ℕ S (k + m) ∷ k + m ∷ e) ((++-assocℕ  (m ↓ k) _ (r ++ℕ nil)) ∙ ap (λ e -> (m ↓ k) ++ℕ _ ∷ e) ++-unit)))
        Sn>>m↓Sk++r = >>-++ (>>-↓ n m (S k) Sn>k+m) Sn>>r
    in  reduction-implies->> (mf , transport (λ e -> n >> e) (! defmf) (>>-++ Sn>>l (>>-++ ((k + m) :⟨ Sn>k+m ⟩: nil) (S (k + m) :⟨ Sn>Sk+m ⟩: Sn>>m↓Sk++r)))) sf p -- 

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
        eqsf = fromLList-++ (l , _) ((k ∷ m ∷ r) , _) ∙ 
               ap fromLList (LList-eq {S n} {(l ++ℕ k ∷ m ∷ r) , _} {(l ++ℕ k ∷ m ∷ r) , Sn>>l++k∷m∷r} idp) ∙ 
               ap (λ e -> <– List≃LList e) (LList-eq {S n} {(l ++ℕ k ∷ m ∷ r) , Sn>>l++k∷m∷r} {sf} (! defmf))
        Sn>>l++m∷k∷r = transport (λ e -> S n >> e) defm (s .snd)
        Sn>>m∷k∷r = >>-implies->> {_} {_} {l} {m ∷ k ∷ r} {nil} (s .snd) (defm ∙ ap (λ e -> l ++ℕ m ∷ k ∷ e) (! ++-unit))
        eqs = fromLList-++ (l , _) ((m ∷ k ∷ r) , _) ∙ 
              ap (λ e -> fromLList {S n} e) (LList-eq {S n} {(l ++ℕ m ∷ k ∷ r) , _} {(l ++ℕ m ∷ k ∷ r) , Sn>>l++m∷k∷r} idp) ∙ 
              ap (<– List≃LList) (LList-eq {S n} {(l ++ℕ m ∷ k ∷ r) , Sn>>l++m∷k∷r} {s} (! defm))
    in  transport2 (λ e f → ReductionRel n e f) eqs eqsf c
reduction-fromLList {n} (s , sp) sf (long≅ {m} k l r .s .(sf .fst) defm defmf) =
    let Sn>>l++↓++x∷r = transport (λ e -> S n >> e) defm sp
        Sn>>l = >>-implies->> {S n} {s} {nil} {l} {S (k + m) ∷ k + m ∷ m ↓ k ++ℕ S (k + m) ∷ r} sp defm
        Sn>k+m = >>-implies-> {S n} {k + m} {s} {l ++ℕ [ S (k + m) ]} {(m ↓ k ++ℕ S (k + m) ∷ r)} sp (defm ∙ ! (++-assocℕ l [ S(k + m) ] _))
        Sn>Sk+m = >>-implies-> {S n} {S (k + m)} {_} {l} {k + m ∷ m ↓ k ++ℕ (1 + k + m) ∷ r} Sn>>l++↓++x∷r idp
        Sn>>r = >>-implies->> {S n} {s} {l ++ℕ S (k + m) ∷ k + m ∷ m ↓ k ++ℕ [ 1 + k + m ]} {r} {nil} sp (defm ∙ 
            ! (++-assocℕ l _ (r ++ℕ nil) ∙ ap (λ e -> l ++ℕ S (k + m) ∷ k + m ∷ e) ((++-assocℕ  (m ↓ k) _ (r ++ℕ nil)) ∙ ap (λ e -> (m ↓ k) ++ℕ _ ∷ e) ++-unit)))
        Sk+m>k = ≤-up2 (≤-up-r-+ rrr)
        Sn>Sk = ≤-transℕ (≤-up2 Sk+m>k) Sn>Sk+m
        ll = <– List≃LList (l , Sn>>l)
        rr = <– List≃LList (r , Sn>>r)
        c = longN≅ ll rr (k + m , <-cancel-S (<– <N≃< Sn>Sk+m)) (k , <-cancel-S (<– <N≃< Sn>Sk)) (<– <N≃< Sk+m>k)
        Sn>>l++x++↓∷r = transport (λ e -> S n >> e) defmf (sf .snd)
        x++↓∷r = [ _ ] ++ℕ _ ∷  ((m ↓ (S k)) ++ℕ r)
        eqsf = fromLList-++ (l , Sn>>l) (x++↓∷r , TODO) ∙ 
               ap fromLList (LList-eq {S n} {(l ++ℕ x++↓∷r) , _} {(l ++ℕ x++↓∷r) , Sn>>l++x++↓∷r} idp) ∙ 
               ap (λ e -> <– List≃LList e) (LList-eq {S n} {(l ++ℕ x++↓∷r) , Sn>>l++x++↓∷r} {sf} (! defmf))
        ↓++x∷r = S (k + m) ∷ k + m ∷ m ↓ k ++ℕ (1 + k + m) ∷ r
        eqs = fromLList-++ (l , _) (↓++x∷r , TODO) ∙ 
              ap (λ e -> fromLList {S n} e) (LList-eq {S n} {(l ++ℕ ↓++x∷r) , _} {(l ++ℕ ↓++x∷r) , Sn>>l++↓++x∷r} idp) ∙ 
              ap (<– List≃LList) (LList-eq {S n} {(l ++ℕ ↓++x∷r) , Sn>>l++↓++x∷r} {(s , sp)} (! defm))
        eqs' = ap (λ e -> (fromLList (l , Sn>>l)) ++ e) TODO
        eqsf' = ap (λ e -> (fromLList (l , Sn>>l)) ++ e) TODO
    in  transport2 (λ e f → ReductionRel n e f) (eqs' ∙ eqs) (eqsf' ∙ eqsf) c

reduction-fromLList* : {n : ℕ} -> (s sf : LList (S n)) -> (p : (s .fst) ≅* (sf .fst)) -> (<– List≃LList s ≅*[ n ] <– List≃LList sf)
reduction-fromLList* {n} (s , sp1) (s , sp2) idp rewrite (>>-eq sp1 sp2) = idpN
reduction-fromLList* {n} s sf (trans≅ {m2 = m2} x p) = 
    let c = reduction-fromLList s (m2 , (reduction-implies->> s m2 (ext x))) x
        rec = reduction-fromLList* {n} _ sf p
    in  transN≅ c rec

reduction-toLList : {n : ℕ} -> (s sf : List (Fin (S n))) -> (p : s ≅[ n ] sf) -> ((–> List≃LList s) .fst) ≅ ((–> List≃LList sf) .fst)
reduction-toLList = TODO

reduction-toLList* : {n : ℕ} -> (s sf : List (Fin (S n))) -> (p : s ≅*[ n ] sf) -> ((–> List≃LList s) .fst) ≅* ((–> List≃LList sf) .fst)
reduction-toLList* = TODO

-- reduction-toLList : {n : ℕ} -> (m mf : LList n) -> ((m .fst) ≅* (mf .fst)) -> (m ≅*[ n ] mf)
-- reduction-toLList = ?

-- {-# NON_TERMINATING #-}
-- LList-to-LehmerProper : {n : ℕ} -> (m : LList n) -> Σ _ (λ nf -> (n ≤ nf) × Σ _ (λ cl -> rev (m .fst) ≅* immersionProper {nf} cl))
-- LList-to-LehmerProper {n} m = 
--   let rn , rcl = Listℕ-to-LehmerProper (m .fst)
--   in {!   !}
