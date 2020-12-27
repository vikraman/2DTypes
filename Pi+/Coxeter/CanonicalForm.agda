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

immersion-transport : {n1 n2 : ℕ} -> (pn : n1 == n2) -> (l : Lehmer n1) -> (immersion l == immersion (transport Lehmer pn l))
immersion-transport {n1} {.n1} idp l = idp

immersionProper-transport : {n1 n2 : ℕ} -> (pn : n1 == n2) -> (l : LehmerProper n1) -> (immersionProper l == immersionProper (transport LehmerProper pn l))
immersionProper-transport {n1} {.n1} idp l = idp

properize : {n : ℕ} -> (cl : Lehmer n) -> Σ _ (λ nf -> Σ _ (λ clf -> (immersion {n} cl == immersionProper {nf} clf) × (nf ≤ n)))
properize CanZ = O , CanZ , idp , z≤n
properize (CanS cl {O} x) = 
  let nrec , clfrec , clfrecp , nfr = properize cl
  in  nrec , clfrec , (++-unit ∙ clfrecp) , ≤-up nfr
properize (CanS {n} cl {S r} x) with properize cl 
... | .0 , CanZ , clfrecp , nfn = (S n) , ((CanS (s≤s z≤n) CanZ x) , ((ap (λ e -> e ++ ((r + n ∸ r) :: (n ∸ r) ↓ r)) clfrecp)) , ≤-reflexive idp )
... | S nrec , CanS {nr} {nfr} pnf clfrec {rr} pnr , clfrecp , nfn = S n , (CanS (s≤s nfn) (CanS pnf clfrec pnr) x) ,  (ap (λ e -> e ++ ((r + n ∸ r) :: (n ∸ r) ↓ r)) clfrecp) , ≤-reflexive idp

unproperize : {n : ℕ} -> (cl : LehmerProper n) -> Σ _ (λ clf -> immersionProper {n} cl == immersion {n} clf)
unproperize CanZ = CanZ , idp
unproperize {S nf} (CanS {n} {.(S nf)} x cl {r} x₁) with unproperize cl
... | nfr , clfr with canonical-lift nf (≤-down2 x) nfr
...    | rec-l , rec-p = CanS rec-l x₁ , ap (λ e -> e ++ (r + nf ∸ r :: nf ∸ r ↓ r)) (clfr ∙ ! rec-p)

-- properize-immersion : {n : ℕ} -> (m : LehmerProper n) -> immersion (fst (unproperize m)) == immersionProper m
-- properize-immersion {0} CanZ = idp
-- properize-immersion {S n} (CanS _ l {r} _) with properize-immersion l
-- ... | q = start+end ({!  !}  ∙ q) (idp {a = r + n ∸ r :: n ∸ r ↓ r})


canonical-proper-append : {n : ℕ} -> (cl : LehmerProper n) -> (x : ℕ) -> (n ≤ x) -> Σ _ (λ clx -> immersionProper {S x} clx == immersionProper {n} cl ++ [ x ])
canonical-proper-append cl x px with unproperize cl
... | upl , upl-p with canonical-append upl x px
...    | (CanS clx {r} SxSx) , clx-p = 
          let nf , clf , clfp , nfp = properize (CanS clx SxSx)
          in  transport LehmerProper (≤-≡ nfp {! SxSx  !}) clf , (((! (immersionProper-transport {!   !} clf)) ∙ ! clfp) ∙ clx-p) ∙ ap (λ e -> e ++ [ x ]) (! upl-p)

-- canonical-proper-append-smaller : {n nf r : ℕ} -> {pn : S n ≤ S nf} -> {pr : S r ≤ S nf} -> {cl : LehmerProper n} -> (x : ℕ) -> (clf : LehmerProper (S nf)) -> (defclf : clf == CanS pn cl pr)
--                                   -> (defx : S x == (nf ∸ r)) -> Σ (S r < S nf) (λ prr -> immersionProper {S nf} (CanS pn cl prr) == (immersionProper {S nf} clf) ++ [ x ])
-- canonical-proper-append-smaller {n} {nf} {r} {pn} {pr} {cl} x clf defclf defx = {!!}

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

lemma : (n r x : ℕ) -> (r ≤ n) -> (cl : Lehmer n) -> (f : (mf : List) -> ((immersion {n} cl ++ ((n ∸ r) ↓ (1 + r))) ++ x :: nil) ≅+ mf -> ⊥) -> (n < x) ⊎ ((x == n ∸ (1 + r)) × (S r ≤ n))
lemma n r x pnr cl f with n <? x
... | yes q = inj₁ q
... | no q with  always-reduces (n ∸ r) r x (≤-trans (≤-down2 (≰⇒> q)) (≤-reflexive (≡-sym (plus-minus pnr))))
... | inj₁ (ar-m , ar-p) =
  let red =
        ≅*begin
          (immersion cl ++ ((n ∸ r) ↓ (1 + r))) ++ x :: nil
        ≅*⟨ idp≅* (++-assoc (immersion cl) _ _) ⟩
          immersion cl ++ ((n ∸ r) ↓ (1 + r)) ++ x :: nil
        ≅*∎
  in  ⊥-elim (f _ (trans*+ red (+l++ (immersion cl) ar-p)))
... | inj₂ qq = inj₂ ({!  !} , {!  !})

lemma-proper : (n r x : ℕ) -> (r ≤ n) -> (cl : LehmerProper n) -> (f : (mf : List) -> ((immersionProper {n} cl ++ ((n ∸ r) ↓ (1 + r))) ++ x :: nil) ≅+ mf -> ⊥) -> (n < x) ⊎ ((x == n ∸ (1 + r)) × (S r ≤ n))
lemma-proper n r x pr cl f with (unproperize cl)
... | ucl , ucl-p = lemma n r x pr ucl (λ mf pp → f _ (transport (λ e -> ((e ++ r + n ∸ r :: n ∸ r ↓ r) ++ x :: nil) ≅+ mf) (! ucl-p) pp))

-- lemma-append : {n : ℕ} -> (cl : Lehmer n) -> (x : ℕ) -> (ll : List) -> (immersion {n} cl == ll) -> Σ ℕ (λ nf → Σ (Lehmer nf) (λ clf → immersion clf == ll ++ x :: nil))
-- lemma-append {n} cl x pcl = {!   !}

-- lemma-reduction : {n : ℕ} -> (x : ℕ) -> (cl : Lehmer n) -> (r : ℕ) -> Σ _ (λ mf -> ((immersion cl ++ S n ∸ r ↓ r) ++ [ x ]) ≅ mf)
-- lemma-reduction {n} x cl r = ?

-- canonical-final≅ (x :: m) f | _ , CanS {S n} (CanS fst₁ x₂) {0} x₁ , snd with (S n) ≤? x
-- ... | yes p = 
--   let tl , tp =  canonical-append ((CanS fst₁ x₂)) x p
--   in  (S x) , (tl , tp ∙ (ap (λ e → e ++ [ x ]) (! ++-unit ∙ snd)))
-- canonical-final≅ (x :: m) f | _ , CanS {S n} (CanS fst₁ {O} x₂) {0} x₁ , snd | no  p = {!   !}
-- canonical-final≅ (x :: m) f | _ , CanS {S n} (CanS fst₁ {S r} x₂) {0} x₁ , snd | no  p = 
--   let x<Sn = ≰⇒> p
--       cl = (S n ∸ (S r) ↓ (S r) ++ [ x ])
--   in  ⊥-elim (f {!   !} {!   !}) -- TODO this requires changing the signature to return LehmerProper instead of just Lehmer - then it will be impossible

-- canonical-final≅ : (m : List) -> (f : (mf : List) -> (rev m ≅* mf) -> ⊥) -> Σ _ (λ n -> Σ _ (λ cl -> immersion {n} cl == rev m))
-- canonical-final≅ nil f = 0 , CanZ , idp
-- canonical-final≅ (x :: m) f with (canonical-final≅ m (λ mf red → f (mf ++ [ x ]) (++r [ x ] red)))
-- canonical-final≅ (x :: m) f | 0 , CanZ , snd rewrite (≡-sym snd) = _ , canonical-append CanZ x z≤n
-- canonical-final≅ (x :: nil) f | _ , CanS {O} CanZ {0} x₁ , snd = _ ,  canonical-append CanZ x z≤n
-- canonical-final≅ (x :: x₂ :: m) f | _ , CanS {O} CanZ {0} x₁ , snd = ⊥-elim (++-abs (! snd))
-- canonical-final≅ (x :: m) f | _ , CanS {S n} (CanS fst₁ x₂) {0} x₁ , snd = {!   !}
-- canonical-final≅ (x :: m) f | _ , CanS {n₁} fst {S r} x₁ , snd  with lemma n₁ r x (≤-down2 x₁) fst (λ mf mf-abs → f mf (transport (λ e -> (e ++ [ x ]) ≅* mf) snd mf-abs))
-- canonical-final≅ (x :: m) f | _ , CanS fst {S r} x₁ , snd | inj₁ x₂ =
--   let rec-m , rec-p = canonical-append (CanS fst {S r} x₁) x x₂
--   in  _ , rec-m , (≡-trans rec-p (start+end snd idp))
-- canonical-final≅ (x :: m) f | _ , CanS {n} fst {S r} x₁ , snd | inj₂ (fst₁ , snd₁) =
--   let tt =
--         begin
--           immersion fst ++ S (r + (n ∸ S r)) :: ((n ∸ S r) ↓ (1 + r))
--         =⟨ start+end (idp {a = immersion fst}) (head+tail (≡-trans (plus-minus snd₁) (≡-sym (plus-minus (≤-down snd₁)))) (≡-sym (++-↓ (n ∸ S r) r))) ⟩
--           immersion fst ++ r + (n ∸ r) :: (S (n ∸ S r) ↓ r) ++ n ∸ S r :: nil
--         =⟨ start+end (idp {a = immersion fst}) (head+tail idp (start+end (cong (λ e -> e ↓ r) (! (∸-up snd₁))) (cong [_]  (≡-sym fst₁)))) ⟩
--           immersion fst ++ r + (n ∸ r) :: ((n ∸ r) ↓ r) ++ x :: nil
--         =⟨ ≡-sym (++-assoc (immersion fst) _ [ x ]) ⟩
--           (immersion fst ++ r + (n ∸ r) :: ((n ∸ r) ↓ r)) ++ x :: nil
--         =⟨ start+end snd (idp {a = [ x ]}) ⟩
--           rev m ++ x :: nil
--         =∎
--   in _ , ((CanS fst {S (S r)} (s≤s snd₁)) , tt)

-- canonical-final≅ : (m : List) -> (f : (mf : List) -> (rev m ≅+ mf) -> ⊥) -> Σ _ (λ n -> Σ _ (λ cl -> immersionProper {n} cl == rev m))
-- canonical-final≅ nil pf = O , CanZ , idp
-- canonical-final≅ (x :: m) f with (canonical-final≅ m (λ mf red → f (mf ++ [ x ]) (++r+ [ x ] red)))
-- ... | O , CanZ , snd  rewrite (≡-sym snd) = _ , canonical-proper-append CanZ x z≤n
-- ... | S fst₁ , CanS x₁ fst₂ {O} x₂ , snd₁ = 
--   let rec = ap (λ e -> e ++ [ x ]) snd₁
--   in  S x , (CanS (s≤s {!   !}) {!   !} (s≤s z≤n) , rec)
-- ... | S fst₁ , CanS x₁ fst₂ {S t} x₂ , snd₁ = {!   !}

canonical-final≅ : (m : List) -> (f : (mf : List) -> (rev m ≅+ mf) -> ⊥) -> Σ _ (λ n -> Σ _ (λ cl -> immersionProper {n} cl == rev m))
canonical-final≅ nil f = O , CanZ , idp
canonical-final≅ (x :: m) f with (canonical-final≅ m (λ mf red → f (mf ++ [ x ]) (++r+ [ x ] red)))
... | n , cl , p with n ≤? x
... | yes q = 
  let ar-cl , ar-p = canonical-proper-append cl x q
  in  S x , ar-cl , (transport (λ e -> immersionProper (fst (canonical-proper-append cl x q)) == e ++ [ x ]) p ar-p)
canonical-final≅ (x :: m) f | O , CanZ , p | no q = ⊥-elim (q z≤n)
canonical-final≅ (x :: m) f | S n , CanS {k} k<Sn cl {r} r<Sn , p | no q =
   let ff = (λ mf pp → f _ ((transport (λ e -> e ++ [ x ] ≅+ mf) p {!   !})))
       lp = lemma-proper n r x (≤-down2 r<Sn) {!   !} ff
   in  {!   !}
  -- let lemma : Σ _ (λ mf -> S (n ∸ r) ↓ r ++ [ x ] ≅ mf)
  --     lemma = {!   !}
  --     rr = +l++ (immersionProper cl) {!   !}
  -- in  ⊥-elim (f _ {!   !})


-- abs-list : {l : List} -> {n : ℕ} -> {r : List} -> (nil == (l ++ (n :: r))) -> ⊥
-- abs-list {nil} {n} {r} ()
-- abs-list {x :: l} {n} {r} ()

-- cut-last : {l1 l2 : List} -> {x1 x2 : ℕ} -> (l1 ++ [ x1 ] == l2 ++ [ x2 ]) -> (l1 == l2)
-- cut-last {nil} {nil} p = idp
-- cut-last {nil} {x :: nil} ()
-- cut-last {nil} {x :: x₁ :: l2} ()
-- cut-last {x :: nil} {nil} ()
-- cut-last {x :: x₁ :: l1} {nil} ()
-- cut-last {x :: l1} {x₁ :: l2} p = head+tail (cut-tail p) (cut-last (cut-head p))

-- cut-last-Lehmer : {n : ℕ} -> {l : List} -> (x : ℕ) -> (cl : LehmerProper n) -> (immersionProper cl == l ++ [ x ]) -> Σ _ (λ nf -> Σ _ (λ clf -> immersionProper {nf} clf == l))
-- cut-last-Lehmer {0} {l} x CanZ pp = ⊥-elim (abs-list pp)
-- cut-last-Lehmer {S n} {l} x (CanS pn cl {0} pr) pp = _ , (cl , cut-last pp)
-- cut-last-Lehmer {S n} {l} x (CanS pn cl {S r} pr) pp =
--   let p1 =
--         begin
--           (immersionProper cl ++ ((1 + (n ∸ S r)) ↓ (1 + r))) ++ [ _ ]
--         =⟨ ++-assoc (immersionProper cl) (S (n ∸ S r) ↓ (1 + r)) _ ⟩
--           _
--         =⟨ start+end (idp {a = immersionProper cl}) (++-↓ (n ∸ S r) (S r)) ⟩
--           immersionProper cl ++ ((n ∸ S r) ↓ (2 + r))
--         =⟨ pp ⟩
--           l ++ [ x ]
--         =∎
--       p2 =
--         begin
--           _
--         =⟨ start+end (idp {a = immersionProper cl}) (head+tail (cong (λ e -> r + e) {!!}) (cong (λ e -> e ↓ r) {!!})) ⟩
--           immersionProper cl ++ r + S (n ∸ S r) :: (S (n ∸ S r) ↓ r)
--         =⟨ cut-last p1 ⟩
--           l
--         =∎
--   in  _ , (CanS pn cl (≤-down pr)) , p2

-- is-canonical? : (m : List) -> BoolDec (Σ _ (λ nf -> Σ _ (λ cl -> immersionProper {nf} cl == rev m)))
-- is-canonical? nil = yes ( _ , (CanZ , idp))
-- is-canonical? (x :: m) with is-canonical? m
-- ... | no  p = no λ {(_ , cl , pp) → p (cut-last-Lehmer x cl pp) }
-- ... | yes (_ , CanZ , pp) rewrite (≡-sym pp) = yes (_ , canonical-proper-append CanZ x z≤n)
-- ... | yes (S nn , CanS {n} {S nn} qn cl {r} qr , pp) with nn <? x
-- ... | yes q =
--   let clx , clp = canonical-proper-append (CanS qn cl qr) x q
--   in  yes (_ , clx , (≡-trans clp (start+end pp idp)))
-- ... | no q with S x ≟ (nn ∸ r)
-- ... | yes qq rewrite (≡-sym pp) =
--   let  prr , app = canonical-proper-append-smaller x (CanS qn cl qr) idp qq
--   in  yes (_ , ((CanS qn cl prr) , app))
-- ... | no qq = no λ {
--   (_ , CanZ , pp) → abs-list pp ;
--   (_ , CanS (s≤s x) CanZ {0} (s≤s z≤n) , ppp) →
--     let m-empty = cut-last {nil} ppp
--     in  abs-list (≡-trans m-empty (≡-sym pp)) ;
--   (_ , CanS x (CanS x₂ cl pr) {0} x₁ , ppp) → {!!} ;
--   (_ , CanS x cl {S r} pr , ppp) → {!!} }

-- canonical-proper-NF : {n : ℕ} -> (cl : LehmerProper n) -> (Σ _ (λ m -> immersionProper {n} cl ≅ m)) -> ⊥
-- canonical-proper-NF cl (m , p) = {!   !}
--   -- let _ , unproper = unproperize cl
--   -- in  final≅-Lehmer unproper _ m idp {!   !} -- (subst (λ e -> e ≅ m) unproper-p p)

-- not-canonical-not-NF : (m : List) -> ¬ (Σ _ (λ n -> Σ _ (λ cl -> (immersionProper {n} cl) == (rev m)))) -> Σ _ (λ mf -> (rev m) ≅ mf)
-- not-canonical-not-NF nil p = ⊥-elim (p (_ , (CanZ , idp)))
-- not-canonical-not-NF (x :: m) p with is-canonical? m
-- -- first, the case when m is not canonical
-- ... | no  q =
--   let rec-m , rec-p = not-canonical-not-NF m q
--   in  _ , (++r+ [ x ] rec-p)
-- -- under this line, we know that m is canonical
-- -- now, lets check if m is empty
-- ... | yes (_ , CanZ , qp) rewrite (≡-sym qp) =
--   let app = canonical-proper-append CanZ x z≤n
--   in  ⊥-elim (p (_ , app))
-- -- under this line, we know that m is not empty
-- -- now check if x is not too big, which will make a Lehmer out of m ++ [ x ]
-- ... | yes ((S nf) , CanS {nf = S nf} pn cl {r} pr , qp) with x ≤? nf
-- ... | no q2 rewrite (≡-sym qp) =
--   let app = canonical-proper-append (CanS pn cl pr) x (≰⇒> q2)
--   in  ⊥-elim (p (_ , app))
-- -- under this line, we know that x is not too big
-- -- now we can finally use the always-reduces
-- ... | yes  q2 with (always-reduces (nf ∸ r) r x (≤-trans q2 (≤-reflexive (≡-sym (plus-minus (≤-down2 pr))))))
--  -- the case when there is a reduction
-- ... | inj₁ (red-m , red-p) rewrite (≡-sym qp) rewrite (plus-minus (≤-down pr)) rewrite (plus-minus (≤-down2 pr)) = _ , trans≅+ {! (l++ (immersionProper cl) red-p) !} {!   !} -- trans (idp≅* (++-assoc (immersionProper cl) _ _)) (l++ (immersionProper cl) red-p)
-- -- the case when x completes the sequence
-- ... | inj₂ q3 rewrite (≡-sym qp) =
--   let prr , app = canonical-proper-append-smaller x (CanS pn cl pr) idp q3
--   in  ⊥-elim (p (_ , (CanS pn cl prr) , app))

-- {-# NON_TERMINATING #-}
-- everything-to-Lehmer : (m : List) -> Σ _ (λ n -> Σ _ (λ cl -> rev m ≅* immersionProper {n} cl))
-- everything-to-Lehmer m with is-canonical? m
-- ... | yes (_ , cl , cl-p) = _ , (cl , (idp≅* (≡-sym cl-p)))
-- ... | no  p =
--   let step-m , step-p = not-canonical-not-NF m p
--       nn , rec-m , rec-p = everything-to-Lehmer (rev step-m)
--   in  nn , rec-m , {!   !} -- (trans step-p (trans (idp≅* rev-rev) rec-p))
