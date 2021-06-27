{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.NonParametrized.LehmerReduction where

open import lib.Base
open import lib.PathOver
open import lib.types.Nat using (_+_ ; ℕ-level)
open import lib.types.Sigma
open import lib.PathGroupoid
open import lib.NType

open import Pi+.Misc
open import Pi+.Common.Arithmetic
open import Pi+.Common.ListN
open import Pi+.Common.LList
open import Pi+.Coxeter.LehmerImmersion
open import Pi+.Coxeter.NonParametrized.ReductionRel
open import Pi+.Coxeter.NonParametrized.ReductionRel+
open import Pi+.Coxeter.NonParametrized.ExchangeLemmas
open import Pi+.Coxeter.NonParametrized.ExchangeLemmas+
open import Pi+.Coxeter.NonParametrized.ImpossibleLists
open import Pi+.Coxeter.NonParametrized.LehmerCanonical

open ≅*-Reasoning

-- LehmerProper represents Lehmers with a non-empty last sequence
data LehmerProper : (n : ℕ) -> Type₀ where
  CanZ : LehmerProper 0
  CanS : {n : ℕ} -> {nf : ℕ} -> (n < nf) -> (l : LehmerProper n) -> {r : ℕ} -> (r < nf) -> LehmerProper nf


immersionProper : {n : ℕ} -> LehmerProper n -> Listℕ
immersionProper {0} CanZ = nil
immersionProper {S n} (CanS _ l {r} _) = (immersionProper l) ++ ((n ∸ r) ↓ (1 + r))

-- (20 ∸ 8) ↓ (1 + 3) = 15 ∷ 14 ∷ 13 ∷ 12 ∷ nil

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
  in  S n , CanS (s≤s nfn) clrec x , (ap (λ e -> e ++ ((r + n ∸ r) ∷ (n ∸ r) ↓ r)) clfrecp) , ≤-reflexive idp

unproperize : {n : ℕ} -> (cl : LehmerProper n) -> Σ _ (λ clf -> immersionProper {n} cl == immersion {n} clf)
unproperize CanZ = CanZ , idp
unproperize {S nf} (CanS {n} {.(S nf)} x cl {r} x₁) =
  let nfr , clfr = unproperize cl
      rec-l , rec-p = canonical-lift nf (≤-down2 x) nfr
  in  CanS rec-l x₁ , ap (λ e -> e ++ (r + nf ∸ r ∷ nf ∸ r ↓ r)) (clfr ∙ ! rec-p)

immersionProper->> : {n : ℕ} -> (cl : LehmerProper n) -> n >> immersionProper cl
immersionProper->> {n} cl =
  let clp , clp-r = unproperize cl
  in  transport (λ e -> n >> e) (! clp-r) (immersion->> clp)


-- properize-fn : {n : ℕ} -> (cl : Lehmer n) -> Σ _ (λ nf → LehmerProper nf)
-- properize-fn cl = let (nf , clf , _) = properize cl in (nf , clf)

-- unproperize-fn : {n : ℕ} -> (cl : LehmerProper n) -> Lehmer n
-- unproperize-fn = fst ∘ unproperize

-- properize∘unproperize-fn-n : {n : ℕ} -> (cl : LehmerProper n) -> n == fst (properize-fn (unproperize-fn cl))
-- properize∘unproperize-fn-n {O} CanZ = idp
-- properize∘unproperize-fn-n {S n} (CanS x cl x₁) = idp

-- properize∘unproperize-fn : {n : ℕ} -> (cl : LehmerProper n) → PathOver LehmerProper (properize∘unproperize-fn-n cl) cl (snd (properize-fn (unproperize-fn cl)))
-- properize∘unproperize-fn {O} CanZ = idp
-- properize∘unproperize-fn {S n} (CanS x cl x₁) =
--   let rec = properize∘unproperize-fn cl
--       t = ap↓ (λ e -> CanS x e x₁) rec
--   in  {!   !}

-- ≡immersionProper : {nf : ℕ} -> (cl1 cl2 : LehmerProper nf) -> (immersionProper {nf} cl1 == immersionProper {nf} cl2) -> cl1 == cl2
-- ≡immersionProper {nf} cl1 cl2 p =
--   let clu1 , clu1-p = unproperize cl1
--       clu2 , clu2-p = unproperize cl2
--       q : unproperize-fn cl1 == unproperize-fn cl2
--       q = ≡immersion clu1 clu2 (! clu1-p ∙ p ∙ clu2-p)

--       -- LehmerProper (fst (properize (fst (unproperize cl1))))
--       qap : PathOver (λ e → LehmerProper (fst (properize e))) q (snd (properize-fn {nf} (unproperize-fn cl1))) (snd (properize-fn {nf} (unproperize-fn cl2)))
--       qap = apd (λ e -> snd (properize-fn {nf} e)) q

--       question : fst (properize-fn {nf} (unproperize-fn cl1)) == fst (properize-fn {nf} (unproperize-fn cl2))
--       question = ap (λ e -> fst (properize e)) q

--       qap' : PathOver LehmerProper question (snd (properize-fn {nf} (unproperize-fn cl1))) ((snd (properize-fn {nf} (unproperize-fn cl2))))
--       qap' = ↓-ap-in LehmerProper (λ x →  fst (properize x)) qap

--       -- ↓-ap-in : u == v [ C ∘ f ↓ p ] → u == v [ C ↓ ap f p ]  -- book, 2.7.somethin
--       -- transport P p u = coe (ap P p) u
--       -- transport P (ap f q) u = coe (ap P (ap f q)) u = coe (ap (P ∘ f) q) u

--       cl1-r' : PathOver LehmerProper (properize∘unproperize-fn-n cl1) cl1 (snd (properize-fn {nf} (unproperize-fn cl1)))
--       cl1-r' = properize∘unproperize-fn cl1
--       cl2-r' : PathOver LehmerProper (properize∘unproperize-fn-n cl2) cl2 (snd (properize-fn {nf} (unproperize-fn cl2)))
--       cl2-r' = properize∘unproperize-fn cl2

--       ttp : nf == nf
--       ttp = (properize∘unproperize-fn-n cl1 ∙ question ∙ ! (properize∘unproperize-fn-n cl2))
--       ttp-idp : ttp == idp
--       ttp-idp = prop-has-all-paths {{has-level-apply ℕ-level nf nf}} ttp idp

--       tt : PathOver LehmerProper ttp cl1 cl2
--       tt = cl1-r' ∙ᵈ qap' ∙ᵈ (!ᵈ cl2-r')

--       t : cl1 == cl2
--       t = transport (λ z → PathOver LehmerProper z cl1 cl2) ttp-idp tt
--   in  t

extractProper-r : {k : ℕ} -> LehmerProper (S k) -> ℕ
extractProper-r (CanS _ _ {r} _) = r

extract-r : {k : ℕ} -> Lehmer (S k) -> ℕ
extract-r (CanS _ {r} _) = r

abstract
  ≡immersion-r : {nf : ℕ} -> (cl1 : Lehmer (S nf)) -> (cl2 : Lehmer (S nf)) -> (immersion {S nf} cl1 == immersion {S nf} cl2) -> (extract-r cl1) == (extract-r cl2)
  ≡immersion-r cl1 cl2 p with (≡immersion cl1 cl2 p)
  ... | idp = idp

  ≡-↓-Proper : (n1 n2 k1 k2 : ℕ) -> ((n1 ↓ S k1) == (n2 ↓ S k2)) -> (n1 == n2) × (k1 == k2)
  ≡-↓-Proper n1 n2 O O p = (cut-tail p) , idp
  ≡-↓-Proper n1 n2 (S k1) (S k2) p =
    let rec-n , rec-k = ≡-↓-Proper n1 n2 k1 k2 (cut-head p)
    in  rec-n , ap S rec-k

>>-up : {n1 n2 : ℕ} -> (n1 ≤ n2) -> {l : Listℕ} -> (n1 >> l) -> (n2 >> l)
>>-up pn nil = nil
>>-up pn (k :⟨ x ⟩: xs) = k :⟨ (≤-trans x pn) ⟩: (>>-up pn xs)

abstract
  ≡-++↓-Proper : (m1 m2 : Listℕ) -> (n1 n2 k1 k2 : ℕ) -> (x1 : S n1 >> m1) -> (x2 : S n2 >> m2) -> (k1 ≤ n1) -> (k2 ≤ n2) -> (m1 ++ ((n1 ∸ k1) ↓ S k1) == m2 ++ ((n2 ∸ k2) ↓ S k2))
    -> (n1 == n2) × (k1 == k2) × (m1 == m2)
  ≡-++↓-Proper nil nil n1 n2 k1 k2 x1 x2 pkn1 pkn2 p =
    let pkn , pk = ≡-↓-Proper (n1 ∸ k1) (n2 ∸ k2) k1 k2 p
        pn = (! (minus-plus {_} {_} {pkn1})) ∙ (≡-up-+ pkn pk) ∙ (minus-plus {_} {_} {pkn2})
    in  pn , (pk , idp)
  ≡-++↓-Proper nil (x ∷ m2) n1 n2 k1 k2 x1 x2 pkn1 pkn2 p =
    ⊥-elim (repeat-spaced-long-lemma (n1 ∸ k1) (S k1) x (k2 + n2 ∸ k2) (≤-trans (≤-down2 (extract-proof x2)) (≤-reflexive (! (plus-minus pkn2)))) nil m2 (n2 ∸ k2 ↓ k2) p)
  ≡-++↓-Proper (x ∷ m1) nil n1 n2 k1 k2 x1 x2 pkn1 pkn2 p =
    let pn , pk , pm = ≡-++↓-Proper nil (x ∷ m1) n2 n1 k2 k1 x2 x1 pkn2 pkn1 (! p)
    in  (! pn) , ((! pk) , (! pm))
  ≡-++↓-Proper (x ∷ m1) (x₁ ∷ m2) n1 n2 k1 k2 (_ :⟨ _ ⟩: x1) (_ :⟨ _ ⟩: x2) pkn1 pkn2 p =
    let pn , pk , pm = ≡-++↓-Proper m1 m2 n1 n2 k1 k2 x1 x2 pkn1 pkn2 (cut-head p)
    in  pn , pk , head+tail (cut-tail p) pm

abstract
  ≡immersionProper-n : {nf1 nf2 : ℕ} -> (cl1 : LehmerProper nf1) -> (cl2 : LehmerProper nf2) -> (immersionProper {nf1} cl1 == immersionProper {nf2} cl2) -> nf1 == nf2
  ≡immersionProper-n CanZ CanZ p = idp
  ≡immersionProper-n (CanS {n1} {S nf1} pn1 cl1 {r1} pr1) CanZ p = ⊥-elim (++-abs-lr p)
  ≡immersionProper-n CanZ (CanS {n2} {S nf2} pn2 cl2 {r2} pr2) p = ⊥-elim (++-abs-lr (! p))
  ≡immersionProper-n (CanS {n1} {S nf1} pn1 cl1 {r1} pr1) (CanS {n2} {S nf2} pn2 cl2 {r2} pr2) p =
    let n1>>cl1 = immersionProper->> cl1
        n2>>cl2 = immersionProper->> cl2
        pn , pk , pm = ≡-++↓-Proper _ _ _ _ _ _ (>>-up (≤-down pn1) n1>>cl1) (>>-up (≤-down pn2) n2>>cl2) (≤-down2 pr1) (≤-down2 pr2) p
    in  ap S pn


≡immersionProper-r : {nf1 nf2 : ℕ} -> (cl1 : LehmerProper (S nf1)) -> (cl2 : LehmerProper (S nf2)) -> (immersionProper {S nf1} cl1 == immersionProper {S nf2} cl2) -> (extractProper-r cl1) == (extractProper-r cl2)
≡immersionProper-r (CanS {n1} {S nf1} pn1 cl1 {r1} pr1) (CanS {n2} {S nf2} pn2 cl2 {r2} pr2) p =
  let n1>>cl1 = immersionProper->> cl1
      n2>>cl2 = immersionProper->> cl2
      pn , pk , pm = ≡-++↓-Proper _ _ _ _ _ _ (>>-up (≤-down pn1) n1>>cl1) (>>-up (≤-down pn2) n2>>cl2) (≤-down2 pr1) (≤-down2 pr2) p
  in  pk


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
... | inj₁ (fst₁ , snd₁) =  inj₁ (_ , (+l++ (S (k + n) ∷ nil) snd₁))
... | inj₂ r = inj₂ r
always-reduces n (S k) x px | no  p =
  let l1 = ≰⇒> p
      l2 = squeeze l1 px
      r = transport (λ e → ((n ↓ (2 + k)) ++ [ e ]) ≅+ ((k + n) ∷ (n ↓ (2 + k)) ++ nil)) (! l2) (long+ {n} k nil nil)
  in  inj₁ (_ , r)

lemma : (n r x : ℕ) -> (r ≤ n) -> (m : Listℕ) -> (f : (mf : Listℕ) -> ((m ++ ((n ∸ r) ↓ (1 + r))) ++ x ∷ nil) ≅+ mf -> ⊥) -> (n < x) ⊎ ((x == n ∸ (1 + r)) × (S r ≤ n))
lemma n r x pnr m f with n <? x
... | yes q = inj₁ q
... | no q with  always-reduces (n ∸ r) r x (≤-trans (≤-down2 (≰⇒> q)) (≤-reflexive (≡-sym (plus-minus pnr))))
... | inj₁ (ar-m , ar-p) =
  let red =
        ≅*begin
          (m ++ ((n ∸ r) ↓ (1 + r))) ++ x ∷ nil
        ≅*⟨ idp≅* (++-assoc m _ _) ⟩
          m ++ ((n ∸ r) ↓ (1 + r)) ++ x ∷ nil
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
      transport (λ e -> r + e ∷ e ↓ r == r + nf ∸ S r ∷ nf ∸ S r ↓ r ) x=nf-Sr idp))) ∙
    ! (++-assoc (immersionProper cl) (r + nf ∸ r ∷ nf ∸ r ↓ r) [ x ]) ∙
    ap (λ e -> immersionProper e ++ [ x ]) (! defclf)

canonical-final≅ : (m : Listℕ) -> (f : (mf : Listℕ) -> (rev m ≅+ mf) -> ⊥) -> Σ _ (λ n -> Σ _ (λ cl -> immersionProper {n} cl == rev m))
canonical-final≅ nil f = O , CanZ , idp
canonical-final≅ (x ∷ m) f with (canonical-final≅ m (λ mf red → f (mf ++ [ x ]) (++r+ [ x ] red)))
... | n , cl , p with n ≤? x
... | yes q =
  let ar-cl , ar-p = canonical-proper-append cl x q
  in  S x , ar-cl , (transport (λ e -> immersionProper (fst (canonical-proper-append cl x q)) == e ++ [ x ]) p ar-p)
canonical-final≅ (x ∷ m) f | O , CanZ , p | no q = ⊥-elim (q z≤n)
canonical-final≅ (x ∷ m) f | S n , CanS {k} k<Sn cl {r} r<Sn , p | no q with lemma n r x (≤-down2 r<Sn) _ (λ mf pp → f _ ((transport (λ e -> e ++ [ x ] ≅+ mf) p pp)))
... | inj₁ qq = ⊥-elim (q qq)
... | inj₂ (fst₁ , snd₁) =
  let prr , prr-p = canonical-proper-append-smaller {k} {n} {r} {k<Sn} {r<Sn} {cl} x (CanS k<Sn cl r<Sn) idp (ap S fst₁ ∙ ! (∸-up snd₁))
  in  S n , (CanS {k} {S n} k<Sn cl {S r} (≤-up2 snd₁) , prr-p ∙ ap (λ e -> e ++ [ x ]) p)

abstract
  abs-Listℕ : {l : Listℕ} -> {n : ℕ} -> {r : Listℕ} -> (nil == (l ++ (n ∷ r))) -> ⊥
  abs-Listℕ {nil} {n} {r} ()
  abs-Listℕ {x ∷ l} {n} {r} ()

cut-last-Lehmer : {n : ℕ} -> {l : Listℕ} -> (x : ℕ) -> (cl : LehmerProper n) -> (immersionProper cl == l ++ [ x ]) -> Σ _ (λ nf -> Σ _ (λ clf -> immersionProper {nf} clf == l))
cut-last-Lehmer {0} {l} x CanZ pp = ⊥-elim (abs-Listℕ pp)
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
          immersionProper cl ++ r + S (n ∸ S r) ∷ (S (n ∸ S r) ↓ r)
        =⟨ cut-last p1 ⟩
          l
        =∎
  in  _ , (CanS pn cl (≤-down pr)) , p2


is-canonical? : (m : Listℕ) -> BoolDec (Σ _ (λ nf -> Σ _ (λ cl -> immersionProper {nf} cl == rev m)))
is-canonical? nil = yes ( _ , (CanZ , idp))
is-canonical? (x ∷ m) with is-canonical? m
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
  (_ , CanZ , pp) → abs-Listℕ pp ;
  (_ , CanS (s≤s x) CanZ {0} (s≤s z≤n) , ppp) →
    let m-empty = cut-last {_} {_} {nil} ppp
    in  abs-Listℕ (≡-trans m-empty (≡-sym pp)) ;
  (S _ , CanS (s≤s x₁) (CanS {_} {n₂} x₂ fst₁ x₃) (s≤s z≤n) , snd₁) ->
    let last = cut-prefix snd₁
        prefix = cut-last snd₁
        n₂=Snf = ≡immersionProper-n (CanS x₂ fst₁ x₃) (CanS qn cl qr) (prefix ∙ ! pp)

        open ≤-Reasoning
        lemma =
          ≤begin
            S x
          ≤⟨ ≰⇒> q ⟩
            S nf
          ≡⟨ ! n₂=Snf ⟩
            n₂
          ≤⟨ x₁ ⟩
            _
          ≡⟨ last ⟩
            x
          ≤∎
    in  1+n≰n lemma ;
    -- S n₁ ∸ m₁
  (S (S _) , CanS {_} {S (S n₁)} (s≤s x₁) fst₁ {S m₁} (s≤s (s≤s x₂)) , snd₁) ->
    let ss = (transport (λ e -> (immersionProper fst₁ ++ m₁ + e ∷ e ↓ m₁) ++ [ n₁ ∸ m₁ ] == (immersionProper fst₁ ++ m₁ + S (n₁ ∸ m₁) ∷ S (n₁ ∸ m₁) ↓ m₁) ++ [ n₁ ∸ m₁ ]) (∸-up-r x₂) idp ∙
            ++-assoc (immersionProper fst₁) (S (n₁ ∸ m₁) ↓ S m₁) [ n₁ ∸ m₁ ]) ∙ ap (λ e -> immersionProper fst₁ ++ e) (++-↓ (n₁ ∸ m₁) (S m₁)) ∙ snd₁
        last = cut-prefix ss
        prefix = cut-last ss
        SSn₁=Snf = ≡immersionProper-n ((CanS (s≤s x₁) fst₁ (≤-up (s≤s x₂)))) (CanS qn cl qr) (prefix ∙ ! pp)
        r₁=r₂ = ≡immersionProper-r ((CanS (s≤s x₁) fst₁ (≤-up (s≤s x₂)))) (CanS qn cl qr) (prefix ∙ ! pp)
    in  qq (ap S (! last) ∙ (∸-up-r x₂ ∙ ap (λ e -> S n₁ ∸ e) r₁=r₂) ∙  ap (λ e -> e ∸ r) (≡-down2 SSn₁=Snf))
  }

canonical-proper-NF : {n : ℕ} -> (cl : LehmerProper n) -> (Σ _ (λ m -> immersionProper {n} cl ≅ m)) -> ⊥
canonical-proper-NF cl (m , p) =
  let unproper , unproper-p = unproperize cl
  in  final≅-Lehmer unproper _ m idp (transport (λ e -> e ≅ m) unproper-p p)

not-canonical-not-NF : (m : Listℕ) -> ¬ (Σ _ (λ n -> Σ _ (λ cl -> (immersionProper {n} cl) == (rev m)))) -> Σ _ (λ mf -> (rev m) ≅+ mf)
not-canonical-not-NF nil p = ⊥-elim (p (_ , (CanZ , idp)))
not-canonical-not-NF (x ∷ m) p with is-canonical? m
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

{-# TERMINATING #-}
Listℕ-to-LehmerProper : (m : Listℕ) -> Σ _ (λ n -> Σ _ (λ cl -> rev m ≅* immersionProper {n} cl))
Listℕ-to-LehmerProper m with is-canonical? m
... | yes (_ , cl , cl-p) = _ , (cl , (idp≅* (≡-sym cl-p)))
... | no  p =
  let step-m , step-p = not-canonical-not-NF m p
      nn , rec-m , rec-p = Listℕ-to-LehmerProper (rev step-m)
  in  nn , rec-m , (trans (ext* step-p) (trans (idp≅* rev-rev) rec-p))

Listℕ-to-Lehmer : (m : Listℕ) -> Σ _ (λ n -> Σ _ (λ cl -> rev m ≅* immersion {n} cl))
Listℕ-to-Lehmer m =
  let n , cl , clp = Listℕ-to-LehmerProper m
      cl' , clp' = unproperize cl
  in  n , (cl' , transport (λ e → rev m ≅* e) clp' clp)
