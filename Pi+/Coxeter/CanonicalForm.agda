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
open import Pi+.Coxeter.CritPairsSwap
open import Pi+.Coxeter.Lehmer

open ≅*-Reasoning

-- LehmerProper represents Lehmers with a non-empty last sequence
data LehmerProper : (n : ℕ) -> Type₀ where
  CanZ : LehmerProper 0
  CanS : {n : ℕ} -> {nf : ℕ} -> (n < nf) -> (l : LehmerProper n) -> {r : ℕ} -> (r < nf) -> LehmerProper nf


immersionProper : {n : ℕ} -> LehmerProper n -> List
immersionProper {0} CanZ = nil
immersionProper {S n} (CanS _ l {r} _) = (immersionProper l) ++ ((n ∸ r) ↓ (1 + r))

properize : {n : ℕ} -> (cl : Lehmer n) -> Σ _ (λ nf -> Σ _ (λ clf -> immersion {n} cl == immersionProper {nf} clf))
properize cl = {!  !}

unproperize : {n : ℕ} -> (cl : LehmerProper n) -> Σ _ (λ nf -> Σ _ (λ clf -> immersionProper {n} cl == immersion {nf} clf))
unproperize cl = {!!}

canonical-proper-append : {n : ℕ} -> (cl : LehmerProper n) -> (x : ℕ) -> (n ≤ x) -> Σ _ (λ clx -> immersionProper {S x} clx == immersionProper {n} cl ++ [ x ])
canonical-proper-append cl x px =
  let _ , upl , upl-p = unproperize cl
      clx , clx-p = canonical-append upl x px
  in  {!!}

canonical-proper-append-smaller : {n nf r : ℕ} -> {pn : S n ≤ S nf} -> {pr : S r ≤ S nf} -> {cl : LehmerProper n} -> (x : ℕ) -> (clf : LehmerProper (S nf)) -> (defclf : clf == CanS pn cl pr)
                                  -> (defx : S x == (nf ∸ r)) -> Σ (S r < S nf) (λ prr -> immersionProper {S nf} (CanS pn cl prr) == (immersionProper {S nf} clf) ++ [ x ])
canonical-proper-append-smaller {n} {nf} {r} {pn} {pr} {cl} x clf defclf defx = {!!}


always-reduces : (n k x : ℕ) -> (x ≤ k + n) -> (Σ _ (λ mf -> (n ↓ (1 + k) ++ [ x ]) ≅* mf)) ⊎ (S x == n)
always-reduces n k x px with S x <? n
... | yes r = inj₁ (_ , (long-swap<-lr x n (1 + k) nil nil r))
... | no r with S x ≟ n
... | yes rr = inj₂ rr
... | no rr with x ≟ n
... | no rrr = {!!}
always-reduces n 0 x px | no r | no rr | yes rr2 rewrite rr2 = inj₁ (_ , (cancel nil nil))
always-reduces n (S k) x px | no r | no rr | yes rr2 with (always-reduces n k x (≤-trans (≤-reflexive rr2) (≤-up-+ rrr)))
always-reduces n (S k) x px | no r | no rr | yes rr2 | inj₁ (rec-m , rec-p) = inj₁ (_ , l++ [ S (k + n) ] rec-p)
always-reduces n (S k) x px | no r | no rr | yes rr2 | inj₂ y = inj₂ y

lemma : (n r x : ℕ) -> (r ≤ n) -> (cl : Lehmer n) -> (f : (mf : List) -> ((immersion {n} cl ++ ((n ∸ r) ↓ (1 + r))) ++ x :: nil) ≅* mf -> ⊥) -> (n < x) ⊎ ((x == n ∸ (1 + r)) × (S r ≤ n))
lemma n r x pnr cl f with n <? x
... | yes q = inj₁ q
... | no q with  always-reduces (n ∸ r) r x (≤-trans (≤-down2 (≰⇒> q)) (≤-reflexive (≡-sym (plus-minus pnr))))
... | inj₁ (ar-m , ar-p) =
  let red =
        ≅*begin
          (immersion cl ++ ((n ∸ r) ↓ (1 + r))) ++ x :: nil
        ≅*⟨ idp≅* (++-assoc (immersion cl) _ _) ⟩
          immersion cl ++ ((n ∸ r) ↓ (1 + r)) ++ x :: nil
        ≅*⟨ l++ (immersion cl) ar-p ⟩
          _
        ≅*∎
  in  ⊥-elim (f _ red)
... | inj₂ qq = inj₂ ({!!} , {!!})

-- canonical-final≅ : (m : List) -> (f : (mf : List) -> (rev m ≅* mf) -> ⊥) -> Σ _ (λ n -> Σ _ (λ cl -> immersion {n} cl == rev m))
-- canonical-final≅ nil f = 0 , CanZ , refl
-- canonical-final≅ (x :: m) f with (canonical-final≅ m (λ mf red → f (mf ++ [ x ]) (++r [ x ] red)))
-- canonical-final≅ (x :: m) f | 0 , CanZ , snd rewrite (≡-sym snd) = _ , canonical-append CanZ x z≤n
-- canonical-final≅ (x :: m) f | _ , CanS fst {0} x₁ , snd = {!!} -- TODO this requires changing the signature to return LehmerProper instead of just Lehmer - then it will be impossible
-- canonical-final≅ (x :: m) f | _ , CanS {n₁} fst {S r} x₁ , snd  with lemma n₁ r x (≤-down2 x₁) fst (λ mf mf-abs → f mf (subst (λ e -> (e ++ [ x ]) ≅* mf) snd mf-abs))
-- canonical-final≅ (x :: m) f | _ , CanS fst {S r} x₁ , snd | inj₁ x₂ =
--   let rec-m , rec-p = canonical-append (CanS fst {S r} x₁) x x₂
--   in  _ , rec-m , (≡-trans rec-p (start+end snd refl))
-- canonical-final≅ (x :: m) f | _ , CanS {n} fst {S r} x₁ , snd | inj₂ (fst₁ , snd₁) =
--   let tt =
--         begin
--           immersion fst ++ S (r + (n ∸ S r)) :: ((n ∸ S r) ↓ (1 + r))
--         =⟨ start+end (idp {a = immersion fst}) (head+tail (≡-trans (plus-minus snd₁) (≡-sym (plus-minus (≤-down snd₁)))) (≡-sym (++-↓ (n ∸ S r) r))) ⟩
--           immersion fst ++ r + (n ∸ r) :: (S (n ∸ S r) ↓ r) ++ n ∸ S r :: nil
--         =⟨ start+end (idp {a = immersion fst}) (head+tail refl (start+end (cong (λ e -> e ↓ r) {!!}) (cong [_]  (≡-sym fst₁)))) ⟩
--           immersion fst ++ r + (n ∸ r) :: ((n ∸ r) ↓ r) ++ x :: nil
--         =⟨ ≡-sym (++-assoc (immersion fst) _ [ x ]) ⟩
--           (immersion fst ++ r + (n ∸ r) :: ((n ∸ r) ↓ r)) ++ x :: nil
--         =⟨ start+end snd (idp {a = [ x ]}) ⟩
--           rev m ++ x :: nil
--         =∎
--   in _ , ((CanS fst {S (S r)} (s≤s snd₁)) , tt)

canonical-final≅ : (m : List) -> (f : (mf : List) -> (rev m ≅* mf) -> ⊥) -> Σ _ (λ n -> Σ _ (λ cl -> immersionProper {n} cl == rev m))
canonical-final≅ m pf = {!!}

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
        =⟨ start+end (idp {a = immersionProper cl}) (head+tail (cong (λ e -> r + e) {!!}) (cong (λ e -> e ↓ r) {!!})) ⟩
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
... | yes (S nn , CanS {n} {S nn} qn cl {r} qr , pp) with nn <? x
... | yes q =
  let clx , clp = canonical-proper-append (CanS qn cl qr) x q
  in  yes (_ , clx , (≡-trans clp (start+end pp idp)))
... | no q with S x ≟ (nn ∸ r)
... | yes qq rewrite (≡-sym pp) =
  let  prr , app = canonical-proper-append-smaller x (CanS qn cl qr) idp qq
  in  yes (_ , ((CanS qn cl prr) , app))
... | no qq = no λ {
  (_ , CanZ , pp) → abs-list pp ;
  (_ , CanS (s≤s x) CanZ {0} (s≤s z≤n) , ppp) →
    let m-empty = cut-last {nil} ppp
    in  abs-list (≡-trans m-empty (≡-sym pp)) ;
  (_ , CanS x (CanS x₂ cl pr) {0} x₁ , ppp) → {!!} ;
  (_ , CanS x cl {S r} pr , ppp) → {!!} }

canonical-proper-NF : {n : ℕ} -> (cl : LehmerProper n) -> (Σ _ (λ m -> immersionProper {n} cl ≅ m)) -> ⊥
canonical-proper-NF cl (m , p) =
  let _ , unproper , unproper-p = unproperize cl
  in  final≅-Lehmer unproper _ m idp {!   !} -- (subst (λ e -> e ≅ m) unproper-p p)

not-canonical-not-NF : (m : List) -> ¬ (Σ _ (λ n -> Σ _ (λ cl -> (immersionProper {n} cl) == (rev m)))) -> Σ _ (λ mf -> (rev m) ≅* mf)
not-canonical-not-NF nil p = ⊥-elim (p (_ , (CanZ , idp)))
not-canonical-not-NF (x :: m) p with is-canonical? m
-- first, the case when m is not canonical
... | no  q =
  let rec-m , rec-p = not-canonical-not-NF m q
  in  _ , (++r [ x ] rec-p)
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
... | inj₁ (red-m , red-p) rewrite (≡-sym qp) rewrite (plus-minus (≤-down pr)) rewrite (plus-minus (≤-down2 pr)) = _ , trans (idp≅* (++-assoc (immersionProper cl) _ _)) (l++ (immersionProper cl) red-p)
-- the case when x completes the sequence
... | inj₂ q3 rewrite (≡-sym qp) =
  let prr , app = canonical-proper-append-smaller x (CanS pn cl pr) idp q3
  in  ⊥-elim (p (_ , (CanS pn cl prr) , app))

{-# NON_TERMINATING #-}
everything-to-Lehmer : (m : List) -> Σ _ (λ n -> Σ _ (λ cl -> rev m ≅* immersionProper {n} cl))
everything-to-Lehmer m with is-canonical? m
... | yes (_ , cl , cl-p) = _ , (cl , (idp≅* (≡-sym cl-p)))
... | no  p =
  let step-m , step-p = not-canonical-not-NF m p
      nn , rec-m , rec-p = everything-to-Lehmer (rev step-m)
  in  nn , rec-m , (trans step-p (trans (idp≅* rev-rev) rec-p))
