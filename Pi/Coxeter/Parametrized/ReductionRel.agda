{-# OPTIONS --without-K --rewriting --termination-depth=2 #-}

module Pi.Coxeter.Parametrized.ReductionRel where

open import lib.Base
open import lib.Relation
open import lib.Equivalence
open import lib.PathFunctor
open import lib.PathGroupoid
open import lib.NType
open import lib.types.Nat
open import lib.types.SetQuotient public
open import lib.types.List
open import lib.types.Fin

open import Pi.Common.Misc
open import Pi.Common.Extra
open import Pi.Common.LList
open import Pi.Common.InequalityEquiv
open import Pi.Common.ListFinLListEquiv
open import Pi.Common.ListN renaming (_++_ to _++ℕ_; ++-assoc to ++-assocℕ)
open import Pi.Coxeter.NonParametrized.ReductionRel
open import Pi.Common.Arithmetic renaming (_<_ to _<ℕ_; ≤-trans to ≤-transℕ)
open import Pi.Common.FinHelpers

syntax DownArrow x y p = x ↓⟨ p ⟩ y

DownArrowH : (m n k : ℕ) -> (n < m) -> (k < m) -> (k < S n) -> List (Fin (S m))
DownArrowH m n O np kp p = S⟨ (n , np) ⟩ :: (⟨ n , np ⟩ :: nil )
DownArrowH m (S n) (S k) np kp p =
    let rec = DownArrowH m n k (<-down np) (<-down kp) (<-cancel-S p)
    in  S⟨ (S n , np) ⟩ :: rec
DownArrowH m O (S k) np kp (ltSR ())

DownArrow : {m : ℕ} -> (n : Fin m) -> (k : Fin m) -> (k ≤^ n) -> List (Fin (S m))
DownArrow {m} (n , np) (k , kp) p = DownArrowH m n k np kp p

DownArrow-== : {m : ℕ} -> {n n' k k' : ℕ} -> {p : k < S n} -> {p' : k' < S n'} -> {pn : n < m} -> {pn' : n' < m} -> {pk : k < m} -> {pk' : k' < m}
    -> (n == n') -> (k == k') -> ((n , pn) ↓⟨ p ⟩ (k , pk)) == ((n' , pn') ↓⟨ p' ⟩ (k' , pk'))
DownArrow-== {m} {n} {n} {k} {k} {p} {p'} {pn} {pn'} {pk} {pk'} idp idp =
    ((n , pn) ↓⟨ p ⟩ (k , pk)) =⟨ ap2 (λ e f -> ((n , e) ↓⟨ p ⟩ (k , f)) ) (<-has-all-paths pn pn') (<-has-all-paths pk pk') ⟩
    ((n , pn') ↓⟨ p ⟩ (k , pk')) =⟨ ap (λ e -> _ ↓⟨ e ⟩ k , pk') (<-has-all-paths p p') ⟩
    ((n , pn') ↓⟨ p' ⟩ (k , pk')) =∎

-- This is saying that toLList preserves down arrow
toLList-↓-w : (m n k : ℕ) -> (np : n < m) -> (kp : k < m) -> (p : k < S n)
    -> (toLList ((n , np) ↓⟨ p ⟩ (k , kp))) == (((n ∸ k) ↓ (S (S k))) , >>-↓ (S m) (n ∸ k) (S (S k))
        (–> <N≃< (<-ap-S (transport (λ e → e < m) (! (plus-minus (≤-down2 (–> <N≃< p)))) np))))
toLList-↓-w m n O np kp p = LList-eq idp
toLList-↓-w m O (S k) np kp (ltSR ())
toLList-↓-w m (S n) (S k) np kp p =
    let rec = toLList-↓-w m n k (<-down np) (<-down kp) (<-cancel-S p)
        rec-r = ap fst rec
    in  LList-eq (head+tail (ap (λ e → S (S e)) (! (plus-minus (≤-down2 (–> <N≃< (<-cancel-S p)))))) rec-r)

toLList-↓ : (m n k : ℕ) -> (np : n < m) -> (kp : k < m) -> (p : k < S n) -> (pl : S m >> ((n ∸ k) ↓ (S (S k))))
    -> (toLList ((n , np) ↓⟨ p ⟩ (k , kp))) == (((n ∸ k) ↓ (S (S k))) , pl)
toLList-↓ m n k np kp p pl = LList-eq (ap fst (toLList-↓-w m n k np kp p))

-- And that fromLList also preserves down arrow
fromLList-↓ : (m n k : ℕ) -> (np : n < m) -> (kp : k < m) -> (p : k < S n) -> (pl : S m >> ((n ∸ k) ↓ (S (S k))))
    -> ((n , np) ↓⟨ p ⟩ (k , kp)) == fromLList (((n ∸ k) ↓ (S (S k))) , pl)
fromLList-↓ m n k np kp p pl =
    let lemma = ap fromLList (toLList-↓ m n k np kp p pl)
    in  ! (fromLList∘toLList _) ∙ lemma

fromLList-↓-w : (m n k : ℕ) -> (np : n < m) -> (kp : k < m) -> (p : k < S n)
    -> ((n , np) ↓⟨ p ⟩ (k , kp)) == fromLList (((n ∸ k) ↓ (S (S k))) , >>-↓ (S m) (n ∸ k) (S (S k))
        (–> <N≃< (<-ap-S (transport (λ e → e < m) (! (plus-minus (≤-down2 (–> <N≃< p)))) np))))
fromLList-↓-w m n k np kp p =
    let lemma = ap fromLList (toLList-↓-w m n k np kp p)
    in  ! (fromLList∘toLList _) ∙ lemma

fromLList-↓-c : (m n k : ℕ) -> (np : k + n < m) -> (kp : k < m) -> (pl : S m >> (n ↓ (S (S k))))
    -> ((k + n , np) ↓⟨ <– <N≃< (≤-up2 (≤-up-r-+ rrr)) ⟩ (k , kp)) == fromLList ((n ↓ (S (S k))) , pl)
fromLList-↓-c m n k np kp pl =
    let lemma = ap fromLList (toLList-↓ m (k + n) k np kp (<– <N≃< (≤-up2 (≤-up-r-+ rrr))) (transport (λ e -> S m >> e ↓ (S (S k))) (! (plus-minus-l {k} {n})) pl))
    in  ! (fromLList∘toLList _) ∙ lemma ∙ ap fromLList (LList-eq (ap (λ e -> e ↓ (S (S k))) (plus-minus-l {k} {n})))


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
        Sn>>l = >>-implies->> {n} {s} {nil} {l} {(m ↓ (S (S k))) ++ℕ (S (k + m)) ∷ r} sp defm
        Sn>k+m = >>-implies-> {n} {k + m} {s} {l ++ℕ [ S (k + m) ]} {(m ↓ k ++ℕ S (k + m) ∷ r)} sp (defm ∙ ! (++-assocℕ l [ S(k + m) ] _))
        Sn>Sk+m = >>-implies-> {n} {S (k + m)} {_} {l} {k + m ∷ m ↓ k ++ℕ (S (k + m)) ∷ r} Sn>>l++↓∷r idp
        Sn>>r = >>-implies->> {n} {s} {l ++ℕ (m ↓ (S (S k))) ++ℕ [ 1 + k + m ]} {r} {nil} sp (defm ∙
            ! (++-assocℕ l _ (r ++ℕ nil) ∙ ap (λ e -> l ++ℕ S (k + m) ∷ k + m ∷ e) ((++-assocℕ  (m ↓ k) _ (r ++ℕ nil)) ∙ ap (λ e -> (m ↓ k) ++ℕ _ ∷ e) ++-unit)))
        Sn>>m↓Sk++r = >>-++ (>>-↓ n m (S k) Sn>k+m) Sn>>r
    in  reduction-implies->> (mf , transport (λ e -> n >> e) (! defmf) (>>-++ Sn>>l (>>-++ ((k + m) :⟨ Sn>k+m ⟩: nil) (S (k + m) :⟨ Sn>Sk+m ⟩: Sn>>m↓Sk++r)))) sf p --

-- Transferring reduction from the case of (LList n) to the case of List (Fin n)
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
        Sn>>l = >>-implies->> {S n} {s} {nil} {l} {(m ↓ (S (S k))) ++ℕ S (k + m) ∷ r} sp defm
        Sn>k+m = >>-implies-> {S n} {k + m} {s} {l ++ℕ [ S (k + m) ]} {(m ↓ k ++ℕ S (k + m) ∷ r)} sp (defm ∙ ! (++-assocℕ l [ S(k + m) ] _))
        Sn>Sk+m = >>-implies-> {S n} {S (k + m)} {_} {l} {k + m ∷ m ↓ k ++ℕ (S (k + m)) ∷ r} Sn>>l++↓++x∷r idp
        Sn>>r = >>-implies->> {S n} {s} {l ++ℕ (m ↓ (S (S k))) ++ℕ [ 1 + k + m ]} {r} {nil} sp (defm ∙
            ! (++-assocℕ l _ (r ++ℕ nil) ∙ ap (λ e -> l ++ℕ S (k + m) ∷ k + m ∷ e) ((++-assocℕ  (m ↓ k) _ (r ++ℕ nil)) ∙ ap (λ e -> (m ↓ k) ++ℕ _ ∷ e) ++-unit)))
        Sk+m>k = ≤-up2 (≤-up-r-+ rrr)
        Sn>Sk = ≤-transℕ (≤-up2 Sk+m>k) Sn>Sk+m
        ll = <– List≃LList (l , Sn>>l)
        rr = <– List≃LList (r , Sn>>r)
        SnN>Sk+m = (<– <N≃< Sn>Sk+m)
        nN>k+m = (<-cancel-S SnN>Sk+m)
        SnN>k+m = (<– <N≃< Sn>k+m)
        nN>k = ((<-cancel-S (<– <N≃< Sn>Sk)))
        Sk+mN>k = (<– <N≃< Sk+m>k)
        c = longN≅ ll rr (k + m , nN>k+m) (k , nN>k) Sk+mN>k
        Sn>>↓ = >>-↓ (S n) m (S (S k)) Sn>Sk+m
        Sn>>x∷r = (_ :⟨ Sn>Sk+m ⟩: Sn>>r)
        Sn>>↓++x∷r = >>-++  Sn>>↓ Sn>>x∷r
        Sn>>l++x++↓∷r = transport (λ e -> S n >> e) defmf (sf .snd)
        x++↓∷r = _ ∷ _ ∷  ((m ↓ (S k)) ++ℕ r)
        Sn>>x++↓∷r = (k + m) :⟨ Sn>k+m ⟩: (>>-++ Sn>>↓ Sn>>r)
        eqsf = fromLList-++ (l , Sn>>l) (x++↓∷r , Sn>>x++↓∷r) ∙
               ap fromLList (LList-eq {S n} {(l ++ℕ x++↓∷r) , _} {(l ++ℕ x++↓∷r) , Sn>>l++x++↓∷r} idp) ∙
               ap (λ e -> <– List≃LList e) (LList-eq {S n} {(l ++ℕ x++↓∷r) , Sn>>l++x++↓∷r} {sf} (! defmf))
        ↓++x∷r = (m ↓ (S (S k))) ++ℕ (S (k + m)) ∷ r


        eqs = fromLList-++ (l , _) (↓++x∷r , Sn>>↓++x∷r) ∙
              ap (λ e -> fromLList {S n} e) (LList-eq {S n} {(l ++ℕ ↓++x∷r) , _} {(l ++ℕ ↓++x∷r) , Sn>>l++↓++x∷r} idp) ∙
              ap (<– List≃LList) (LList-eq {S n} {(l ++ℕ ↓++x∷r) , Sn>>l++↓++x∷r} {(s , sp)} (! defm))
        trm = <-cancel-S (<– <N≃<
                (≤-transℕ (≤-up2 (≤-up2 (≤-up-r-+ rrr)))
                    (>>-implies-> (transport (λ e → S n >> e) defm sp) idp)))
        p1 =  _
            =⟨ ap2 (λ e f -> e ++ f) idp (List=-out (pair= idp (<-has-all-paths _ _) , idp)) ⟩
              ((k + m , _) ↓⟨ _ ⟩ (k , trm)) ++ (fromLList (((S (k + m)) ∷ r) , Sn>>x∷r))
            =⟨ ap (λ e -> e ++ (fromLList (((S (k + m)) ∷ r) , Sn>>x∷r))) (fromLList-↓-c n m k nN>k+m nN>k Sn>>↓) ⟩
              fromLList ((m ↓ (S (S k))) , (>>-↓ (S n) m (S (S k)) Sn>Sk+m)) ++ fromLList ((S (k + m) ∷ r) , Sn>>x∷r)
            =⟨ fromLList-++ ((m ↓ (S (S k))) , Sn>>↓) ((S (k + m) ∷ r) , Sn>>x∷r) ⟩
              fromLList (((m ↓ (S (S k)) ++ℕ (S (k + m) ∷ r)) , >>-++ Sn>>↓ Sn>>x∷r))
            =∎
        p1' = ((k + m , _) ↓⟨ _ ⟩ (k , trm)) ++ (fromLList (r , Sn>>r))
            =⟨ ap (λ e -> e ++ (fromLList (r , Sn>>r))) (fromLList-↓-c n m k nN>k+m nN>k Sn>>↓) ⟩
              fromLList ((m ↓ (S (S k))) , (>>-↓ (S n) m (S (S k)) Sn>Sk+m)) ++ fromLList (r , Sn>>r)
            =⟨ fromLList-++ ((m ↓ (S (S k))) , Sn>>↓) (r , Sn>>r) ⟩
              fromLList (((m ↓ (S (S k)) ++ℕ r) , >>-++ Sn>>↓ Sn>>r))
            =∎
        p2 = List=-out ((pair= idp (<-has-all-paths _ _)) , p1')
        eqs' = ap (λ e -> (fromLList (l , Sn>>l)) ++ e) p1
        eqsf' = ap (λ e -> (fromLList (l , Sn>>l)) ++ e) p2
    in  transport2 (λ e f → ReductionRel n e f) (eqs' ∙ eqs) (eqsf' ∙ eqsf) c

reduction-fromLList* : {n : ℕ} -> (s sf : LList (S n)) -> (p : (s .fst) ≅* (sf .fst)) -> (<– List≃LList s ≅*[ n ] <– List≃LList sf)
reduction-fromLList* {n} (s , sp1) (s , sp2) idp rewrite (>>-eq sp1 sp2) = idpN
reduction-fromLList* {n} s sf (trans≅ {m2 = m2} x p) =
    let c = reduction-fromLList s (m2 , (reduction-implies->> s m2 (ext x))) x
        rec = reduction-fromLList* {n} _ sf p
    in  transN≅ c rec

-- And from List (Fin n) to LList n
reduction-toLList : {n : ℕ} -> (s sf : List (Fin (S n))) -> (p : s ≅[ n ] sf) -> ((–> List≃LList s) .fst) ≅ ((–> List≃LList sf) .fst)
reduction-toLList _ _ (cancelN≅ l r m) =
    let ll = (–> List≃LList l) .fst
        rr = (–> List≃LList r) .fst
        c = cancel≅ {m .fst} ll rr _ _ idp idp
    in  transport2 (λ e f -> e ≅ f) (! (toLList-++ l (m :: m :: r))) (! (toLList-++ l r)) c
reduction-toLList _ _ (swapN≅ l r m k x) =
    let ll = (–> List≃LList l) .fst
        rr = (–> List≃LList r) .fst
        c = swap≅ {m .fst} {k .fst} (–> <N≃< x) ll rr _ _ idp idp
    in  transport2 (λ e f -> e ≅ f) (! (toLList-++ l (_ :: _ :: r))) (! (toLList-++ l (_ :: _ :: r))) c
reduction-toLList {S n} _ _ (longN≅ l r (m , mp) (k , kp) p) =
    let ll = (–> List≃LList l) .fst
        rr = (–> List≃LList r) .fst
        c = long≅ {m ∸ k} k ll rr _ _ idp idp
        p1 =  ((toLList l) .fst) ++ℕ (((m ∸ k) ↓ (S (S k))) ++ℕ S (k + m ∸ k) ∷ toLList r .fst)
            =⟨ ap (λ e → toLList l .fst ++ℕ m ∸ k ↓ S (S k) ++ℕ S e ∷ toLList r .fst) (plus-minus (≤-down2 (–> <N≃< p))) ⟩
              ((toLList l) .fst) ++ℕ (((m ∸ k) ↓ (S (S k))) ++ℕ (S m ∷ toLList r .fst))
            =⟨ ap (λ e → toLList l .fst ++ℕ e ++ℕ S m ∷ toLList r .fst) (! (ap fst (toLList-↓-w (S n) m k mp kp p))) ⟩
              ((toLList l) .fst) ++ℕ (toLList ((m , mp) ↓⟨ p ⟩ (k , kp)) .fst ++ℕ toLList (((S m , <-ap-S mp) :: r)) .fst)
            =⟨ ap (λ e → toLList l .fst ++ℕ e) (! (toLList-++ ((m , mp) ↓⟨ p ⟩ (k , kp)) ((S m , <-ap-S mp) :: r))) ⟩
              ((toLList l) .fst) ++ℕ (toLList (((m , mp) ↓⟨ p ⟩ (k , kp)) ++ ((S m , <-ap-S mp) :: r))) .fst
            =⟨ ! (toLList-++ l (((m , mp) ↓⟨ p ⟩ (k , kp)) ++ ((S m , <-ap-S mp) :: r))) ⟩
              toLList (l ++ (((m , mp) ↓⟨ p ⟩ (k , kp)) ++ ((S m , <-ap-S mp) :: r))) .fst
            =∎
        p2 = ((toLList l) .fst) ++ℕ ((k + m ∸ k) ∷ ((m ∸ k) ↓ (S (S k))) ++ℕ toLList r .fst)
            =⟨ ap (λ e → toLList l .fst ++ℕ e ∷ m ∸ k ↓ S (S k) ++ℕ toLList r .fst) (plus-minus (≤-down2 (–> <N≃< p))) ⟩
              ((toLList l) .fst) ++ℕ (m ∷ ((m ∸ k) ↓ (S (S k))) ++ℕ toLList r .fst)
            =⟨ ap (λ e → toLList l .fst ++ℕ m ∷ (e ++ℕ toLList r .fst)) (! (ap fst ((toLList-↓-w (S n) m k mp kp p)))) ⟩
              ((toLList l) .fst) ++ℕ _ ∷ (toLList ((m , mp) ↓⟨ p ⟩ (k , kp)) .fst ++ℕ toLList r .fst)
            =⟨ ap (λ e → toLList l .fst ++ℕ e) (! (toLList-++ ((m , ltSR mp) :: ((m , mp) ↓⟨ p ⟩ (k , kp))) r)) ⟩
              ((toLList l) .fst) ++ℕ toLList ((m , ltSR mp) :: (((m , mp) ↓⟨ p ⟩ (k , kp)) ++ r)) .fst
            =⟨ ! (toLList-++ l ((_ :: ((m , mp) ↓⟨ p ⟩ (k , kp))) ++ r)) ⟩
              toLList (l ++ ((m , ltSR mp) :: ((m , mp) ↓⟨ p ⟩ (k , kp)) ++ r)) .fst
            =∎
    in  transport2 (λ e f -> e ≅ f) p1 p2 c

reduction-toLList* : {n : ℕ} -> (s sf : List (Fin (S n))) -> (p : s ≅*[ n ] sf) -> ((–> List≃LList s) .fst) ≅* ((–> List≃LList sf) .fst)
reduction-toLList* s .s idpN = idp
reduction-toLList* s sf (transN≅ x p) = trans≅ (reduction-toLList _ _ x) (reduction-toLList* _ _ p)
