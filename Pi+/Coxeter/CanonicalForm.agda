{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module Pi+.Coxeter.CanonicalForm where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.PathGroupoid

open import Pi+.Misc
open import Pi+.Coxeter.Arithmetic
open import Pi+.Coxeter.Lists
open import Pi+.Coxeter.ReductionRel
open import Pi+.Coxeter.ReductionRel+
open import Pi+.Coxeter.ExchangeLemmas
open import Pi+.Coxeter.ExchangeLemmas+
open import Pi+.Coxeter.Lehmer

open ≅*-Reasoning

-- LehmerProper represents Lehmers with a non-empty last sequence
data LehmerProper : (n : ℕ) -> Type₀ where
  CanZ : LehmerProper 0
  CanS : {n : ℕ} -> {nf : ℕ} -> (n < nf) -> (l : LehmerProper n) -> {r : ℕ} -> (r < nf) -> LehmerProper nf

immersionProper : {n : ℕ} -> LehmerProper n -> List
immersionProper {0} CanZ = nil
immersionProper {S n} (CanS _ l {r} _) = (immersionProper l) ++ ((n ∸ r) ↓ (1 + r))

-- (20 ∸ 8) ↓ (1 + 3) = 15 :: 14 :: 13 :: 12 :: nil

immersion-transport : {n1 n2 : ℕ} -> (pn : n1 == n2) -> (l : Lehmer n1) -> (immersion l == immersion (transport Lehmer pn l))
immersion-transport {n1} {.n1} idp l = idp

immersionProper-transport : {n1 n2 : ℕ} -> (pn : n1 == n2) -> (l : LehmerProper n1) -> (immersionProper l == immersionProper (transport LehmerProper pn l))
immersionProper-transport {n1} {.n1} idp l = idp

properize : {n : ℕ} -> (cl : Lehmer n) -> Σ _ (λ nf -> Σ _ (λ clf -> (immersion {n} cl == immersionProper {nf} clf) × (nf ≤ n)))
properize CanZ = O , CanZ , idp , z≤n
properize (CanS cl {O} x) = 
  let nrec , clfrec , clfrecp , nfr = properize cl
  in  nrec , clfrec , (++-unit ∙ clfrecp) , ≤-up nfr
properize (CanS {n} cl {S r} x) =
  let (k , clrec , clfrecp , nfn) = properize cl
  in  S n , CanS (s≤s nfn) clrec x , (ap (λ e -> e ++ ((r + n ∸ r) :: (n ∸ r) ↓ r)) clfrecp) , ≤-reflexive idp

unproperize : {n : ℕ} -> (cl : LehmerProper n) -> Σ _ (λ clf -> immersionProper {n} cl == immersion {n} clf)
unproperize CanZ = CanZ , idp
unproperize {S nf} (CanS {n} {.(S nf)} x cl {r} x₁) =
  let nfr , clfr = unproperize cl 
      rec-l , rec-p = canonical-lift nf (≤-down2 x) nfr
  in  CanS rec-l x₁ , ap (λ e -> e ++ (r + nf ∸ r :: nf ∸ r ↓ r)) (clfr ∙ ! rec-p)


canonical-proper-append : {n : ℕ} -> (cl : LehmerProper n) -> (x : ℕ) -> (n ≤ x) -> Σ _ (λ clx -> immersionProper {S x} clx == immersionProper {n} cl ++ [ x ])
canonical-proper-append cl x px with unproperize cl
... | upl , upl-p with canonical-append upl x px
...    | clx , clx-p = 
          let nf , clf , clfp , nfp = properize (CanS {x} clx {1} (≤-up2 z≤n))
          in  transport LehmerProper (≤-≡ nfp rrr) clf , ((! ((immersionProper-transport ((≤-≡ (s≤s (≤-reflexive idp)) (s≤s (≤-reflexive idp)))) clf)) ∙ ! clfp) ∙ clx-p) ∙ ap (λ e -> e ++ [ x ]) (! upl-p)


always-reduces : (n k x : ℕ) -> (x ≤ k + n) -> (Σ _ (λ mf -> (n ↓ (1 + k) ++ [ x ]) ≅+ mf)) ⊎ (S x == n)
always-reduces n O x px with n ≤? x
... | yes p rewrite (≤-≡ p px) = inj₁ (_ , (cancel+ nil nil))
... | no  p with S x ≟ n
... | yes r = inj₂ r
... | no  r with S x <? n
... | yes rr = inj₁ (_ , (swap+ rr nil nil))
... | no  rr =
  let l1 = ≰⇒> p
      l2 = ≰⇒> rr
  in  ⊥-elim (nowhere rr r (λ x₁ → 1+n≰n (≤-trans (≤-reflexive (! x₁)) l1)) λ x₁ → p (≤-down2 (≤-down x₁)))
always-reduces n (S k) x px with x ≤? k + n
... | yes p with always-reduces n k x p
... | inj₁ (fst₁ , snd₁) =  inj₁ (_ , (+l++ (S (k + n) :: nil) snd₁))
... | inj₂ r = inj₂ r
always-reduces n (S k) x px | no  p = 
  let l1 = ≰⇒> p
      l2 = squeeze l1 px
      r = transport (λ e → ((n ↓ (2 + k)) ++ [ e ]) ≅+ ((k + n) :: (n ↓ (2 + k)) ++ nil)) (! l2) (long+ {n} k nil nil)
  in  inj₁ (_ , r)

lemma : (n r x : ℕ) -> (r ≤ n) -> (m : List) -> (f : (mf : List) -> ((m ++ ((n ∸ r) ↓ (1 + r))) ++ x :: nil) ≅+ mf -> ⊥) -> (n < x) ⊎ ((x == n ∸ (1 + r)) × (S r ≤ n))
lemma n r x pnr m f with n <? x
... | yes q = inj₁ q
... | no q with  always-reduces (n ∸ r) r x (≤-trans (≤-down2 (≰⇒> q)) (≤-reflexive (≡-sym (plus-minus pnr))))
... | inj₁ (ar-m , ar-p) =
  let red =
        ≅*begin
          (m ++ ((n ∸ r) ↓ (1 + r))) ++ x :: nil
        ≅*⟨ idp≅* (++-assoc m _ _) ⟩
          m ++ ((n ∸ r) ↓ (1 + r)) ++ x :: nil
        ≅*∎
  in  ⊥-elim (f _ (trans*+ red (+l++ m ar-p)))
... | inj₂ qq = 
  let 1+x+r=n = eliminate-∸ pnr qq
      r<n = introduce-≤-from-+ (ap S (+-comm r x) ∙ 1+x+r=n)
  in  inj₂ (≡-down2 (qq ∙ ∸-up {n} {r} r<n) , r<n)

canonical-proper-append-smaller : {n nf r : ℕ} -> {pn : S n ≤ S nf} -> {pr : S r ≤ S nf} -> {cl : LehmerProper n} -> (x : ℕ) -> (clf : LehmerProper (S nf)) -> (defclf : clf == CanS pn cl pr)
                                  -> (defx : S x == (nf ∸ r)) -> Σ (S r < S nf) (λ prr -> immersionProper {S nf} (CanS pn cl prr) == (immersionProper {S nf} clf) ++ [ x ])
canonical-proper-append-smaller {n} {nf} {r} {pn} {pr} {cl} x clf defclf defx = 
  let x+Sr=nf = ≡-down2 (eliminate-∸ pr defx)
      r<nf = introduce-≤-from-+ {S r} {x} {nf} (ap S (+-comm r x) ∙ (! (+-three-assoc {x} {1} {r})) ∙ x+Sr=nf)
      x=nf-Sr = ! (introduce-∸ r<nf x+Sr=nf)
      lemma = ++-↓ (nf ∸ r) r
  in  ≤-up2 r<nf , 
    ap (λ e -> immersionProper cl ++ e) (head+tail ((plus-minus {S r} {nf} r<nf) ∙ (! (plus-minus {r} {nf} (≤-down r<nf)))) (! (++-↓-S (nf ∸ r) r x defx ∙ 
      transport {!   !} x=nf-Sr {!   !}))) ∙ 
    ! (++-assoc (immersionProper cl) (r + nf ∸ r :: nf ∸ r ↓ r) [ x ]) ∙ 
    ap (λ e -> immersionProper e ++ [ x ]) (! defclf)

canonical-final≅ : (m : List) -> (f : (mf : List) -> (rev m ≅+ mf) -> ⊥) -> Σ _ (λ n -> Σ _ (λ cl -> immersionProper {n} cl == rev m))
canonical-final≅ nil f = O , CanZ , idp
canonical-final≅ (x :: m) f with (canonical-final≅ m (λ mf red → f (mf ++ [ x ]) (++r+ [ x ] red)))
... | n , cl , p with n ≤? x
... | yes q = 
  let ar-cl , ar-p = canonical-proper-append cl x q
  in  S x , ar-cl , (transport (λ e -> immersionProper (fst (canonical-proper-append cl x q)) == e ++ [ x ]) p ar-p)
canonical-final≅ (x :: m) f | O , CanZ , p | no q = ⊥-elim (q z≤n)
canonical-final≅ (x :: m) f | S n , CanS {k} k<Sn cl {r} r<Sn , p | no q with lemma n r x (≤-down2 r<Sn) _ (λ mf pp → f _ ((transport (λ e -> e ++ [ x ] ≅+ mf) p pp)))
... | inj₁ qq = ⊥-elim (q qq)
... | inj₂ (fst₁ , snd₁) = 
  let prr , prr-p = canonical-proper-append-smaller {k} {n} {r} {k<Sn} {r<Sn} {cl} x (CanS k<Sn cl r<Sn) idp (ap S fst₁ ∙ ! (∸-up snd₁))
  in  S n , (CanS {k} {S n} k<Sn cl {S r} (≤-up2 snd₁) , prr-p ∙ ap (λ e -> e ++ [ x ]) p)


abs-list : {l : List} -> {n : ℕ} -> {r : List} -> (nil == (l ++ (n :: r))) -> ⊥
abs-list {nil} {n} {r} ()
abs-list {x :: l} {n} {r} ()

cut-last : {l1 l2 : List} -> {x1 x2 : ℕ} -> (l1 ++ [ x1 ] == l2 ++ [ x2 ]) -> (l1 == l2)
cut-last {nil} {nil} p = idp
cut-last {nil} {x :: nil} ()
cut-last {nil} {x :: x₁ :: l2} ()
cut-last {x :: nil} {nil} ()
cut-last {x :: x₁ :: l1} {nil} ()
cut-last {x :: l1} {x₁ :: l2} p = head+tail (cut-tail p) (cut-last (cut-head p))

cut-last-Lehmer : {n : ℕ} -> {l : List} -> (x : ℕ) -> (cl : LehmerProper n) -> (immersionProper cl == l ++ [ x ]) -> Σ _ (λ nf -> Σ _ (λ clf -> immersionProper {nf} clf == l))
cut-last-Lehmer {0} {l} x CanZ pp = ⊥-elim (abs-list pp)
cut-last-Lehmer {S n} {l} x (CanS pn cl {0} pr) pp = _ , (cl , cut-last pp)
cut-last-Lehmer {S n} {l} x (CanS pn cl {S r} pr) pp =
  let p1 =
        begin
          (immersionProper cl ++ ((1 + (n ∸ S r)) ↓ (1 + r))) ++ [ _ ]
        =⟨ ++-assoc (immersionProper cl) (S (n ∸ S r) ↓ (1 + r)) _ ⟩
          _
        =⟨ start+end (idp {a = immersionProper cl}) (++-↓ (n ∸ S r) (S r)) ⟩
          immersionProper cl ++ ((n ∸ S r) ↓ (2 + r))
        =⟨ pp ⟩
          l ++ [ x ]
        =∎
      p2 =
        begin
          _
        =⟨ start+end (idp {a = immersionProper cl}) (head+tail (cong (λ e -> r + e) (∸-up pr)) (cong (λ e -> e ↓ r) (∸-up pr))) ⟩
          immersionProper cl ++ r + S (n ∸ S r) :: (S (n ∸ S r) ↓ r)
        =⟨ cut-last p1 ⟩
          l
        =∎
  in  _ , (CanS pn cl (≤-down pr)) , p2

is-canonical? : (m : List) -> BoolDec (Σ _ (λ nf -> Σ _ (λ cl -> immersionProper {nf} cl == rev m)))
is-canonical? nil = yes ( _ , (CanZ , idp))
is-canonical? (x :: m) with is-canonical? m
... | no  p = no λ {(_ , cl , pp) → p (cut-last-Lehmer x cl pp) }
... | yes (_ , CanZ , pp) rewrite (≡-sym pp) = yes (_ , canonical-proper-append CanZ x z≤n)
... | yes (S nf , CanS {n} {S nf} qn cl {r} qr , pp) with nf <? x
...   | yes q =
    let clx , clp = canonical-proper-append (CanS qn cl qr) x q
    in  yes (_ , clx , (≡-trans clp (start+end pp idp)))
... | no q with S x ≟ (nf ∸ r)
... | yes qq rewrite (≡-sym pp) =
  let  prr , app = canonical-proper-append-smaller x (CanS qn cl qr) idp qq
  in  yes (_ , ((CanS qn cl prr) , app))
... | no qq = no λ {
  (_ , CanZ , pp) → abs-list pp ;
  (_ , CanS (s≤s x) CanZ {0} (s≤s z≤n) , ppp) →
    let m-empty = cut-last {nil} ppp
    in  abs-list (≡-trans m-empty (≡-sym pp)) ;
  (_ , CanS {0} {S (S n₁)} (s≤s x₁) CanZ {S m₁} (s≤s (s≤s x₂)), snd₁) -> {!   !} ;
  (_ , CanS (s≤s x₁) (CanS x₂ fst₁ x₃) {O} x₄ , snd₁) -> {!   !} ;
  (_ , CanS (s≤s x₁) (CanS x₂ fst₁ x₃) {S r} x₄ , snd₁) -> {!   !}
  }

canonical-proper-NF : {n : ℕ} -> (cl : LehmerProper n) -> (Σ _ (λ m -> immersionProper {n} cl ≅ m)) -> ⊥
canonical-proper-NF cl (m , p) = 
  let unproper , unproper-p = unproperize cl
  in  final≅-Lehmer unproper _ m idp (transport (λ e -> e ≅ m) unproper-p p)

not-canonical-not-NF : (m : List) -> ¬ (Σ _ (λ n -> Σ _ (λ cl -> (immersionProper {n} cl) == (rev m)))) -> Σ _ (λ mf -> (rev m) ≅+ mf)
not-canonical-not-NF nil p = ⊥-elim (p (_ , (CanZ , idp)))
not-canonical-not-NF (x :: m) p with is-canonical? m
-- first, the case when m is not canonical
... | no  q =
  let rec-m , rec-p = not-canonical-not-NF m q
  in  _ , (++r+ [ x ] rec-p)
-- under this line, we know that m is canonical
-- now, lets check if m is empty
... | yes (_ , CanZ , qp) rewrite (≡-sym qp) =
  let app = canonical-proper-append CanZ x z≤n
  in  ⊥-elim (p (_ , app))
-- under this line, we know that m is not empty
-- now check if x is not too big, which will make a Lehmer out of m ++ [ x ]
... | yes ((S nf) , CanS {nf = S nf} pn cl {r} pr , qp) with x ≤? nf
... | no q2 rewrite (≡-sym qp) =
  let app = canonical-proper-append (CanS pn cl pr) x (≰⇒> q2)
  in  ⊥-elim (p (_ , app))
-- under this line, we know that x is not too big
-- now we can finally use the always-reduces
... | yes  q2 with (always-reduces (nf ∸ r) r x (≤-trans q2 (≤-reflexive (≡-sym (plus-minus (≤-down2 pr))))))
 -- the case when there is a reduction
... | inj₁ (red-m , red-p) rewrite (≡-sym qp) rewrite (plus-minus (≤-down pr)) rewrite (plus-minus (≤-down2 pr)) = _ , trans*+ (idp≅* (++-assoc (immersionProper cl) _ _)) (+l++ (immersionProper cl) red-p)
-- the case when x completes the sequence
... | inj₂ q3 rewrite (≡-sym qp) =
  let prr , app = canonical-proper-append-smaller x (CanS pn cl pr) idp q3
  in  ⊥-elim (p (_ , (CanS pn cl prr) , app))

{-# NON_TERMINATING #-}
everything-to-LehmerProper : (m : List) -> Σ _ (λ n -> Σ _ (λ cl -> rev m ≅* immersionProper {n} cl))
everything-to-LehmerProper m with is-canonical? m
... | yes (_ , cl , cl-p) = _ , (cl , (idp≅* (≡-sym cl-p)))
... | no  p =
  let step-m , step-p = not-canonical-not-NF m p
      nn , rec-m , rec-p = everything-to-LehmerProper (rev step-m)
  in  nn , rec-m , (trans (ext* step-p) (trans (idp≅* rev-rev) rec-p))

{-# NON_TERMINATING #-}
everything-to-Lehmer : (m : List) -> Σ _ (λ n -> Σ _ (λ cl -> rev m ≅* immersion {n} cl))
everything-to-Lehmer m = 
  let n , cl , clp = everything-to-LehmerProper m
      cl' , clp' = unproperize cl
  in  n , (cl' , transport (λ e → rev m ≅* e) clp' clp)