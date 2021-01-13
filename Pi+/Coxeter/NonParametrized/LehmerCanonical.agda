{-# OPTIONS --without-K --rewriting --termination-depth=2 #-}

module Pi+.Coxeter.NonParametrized.LehmerCanonical where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.types.Sigma
open import lib.NType
open import lib.PathGroupoid

open import Pi+.Misc
open import Pi+.Coxeter.Common.Arithmetic
open import Pi+.Coxeter.Common.ListN
open import Pi+.Coxeter.Common.LList
open import Pi+.Coxeter.Common.Lehmer
open import Pi+.Coxeter.NonParametrized.ReductionRel
open import Pi+.Coxeter.NonParametrized.ImpossibleLists
open import Pi+.Coxeter.NonParametrized.MCoxeter

open ≅*-Reasoning

canonical-lift : {n : ℕ} -> (m : ℕ) -> (n ≤ m) -> (cln : Lehmer n) -> Σ (Lehmer m) (λ clm -> immersion {m} clm == immersion {n} cln)
canonical-lift {n} m p cln with ≤-∃ _ _ p
canonical-lift {.m} m p cln | 0 , idp = cln , idp
canonical-lift {n} .(S (fst + n)) p cln | S fst , idp =
  let rec-m , rec-p = canonical-lift {n} (fst + n) (≤-up-+ rrr) cln
  in  (CanS rec-m z≤n) , (≡-trans ++-unit rec-p)

canonical-append : {n : ℕ} -> (cl : Lehmer n) -> (x : ℕ) -> (n ≤ x) -> Σ (Lehmer x) (λ clx -> immersion {S x} (CanS {x} clx {1} (≤-up2 z≤n)) == immersion {n} cl ++ [ x ])
canonical-append cl x px =
  let lifted-m , lifted-p = canonical-lift x px cl
  in  lifted-m , start+end lifted-p idp

lehmer-eta : {n : ℕ} -> {cl1 cl2 : Lehmer n} -> {r1 r2 : ℕ} -> (rn1 : r1 ≤ (S n)) -> (rn2 : r2 ≤ (S n)) -> (cl1 == cl2) -> (r1 == r2) -> (CanS cl1 rn1) == (CanS cl2 rn2)
lehmer-eta rn1 rn2 idp idp = ap (CanS _) (prop-has-all-paths rn1 rn2) -- TODO: write with ap/uncurry, without path induction

final≅-↓ : (n k1 : ℕ) -> (m : Listℕ) -> (n ↓ k1) ≅ m -> ⊥
final≅-↓ n k1 m (cancel≅ {n₁} l r .(n ↓ k1) .m defm defmf) = repeat-long-lemma n k1 n₁ l r defm
final≅-↓ n k1 m (swap≅ x l r .(n ↓ k1) .m defm defmf) = incr-long-lemma _ _ _ _ x l r defm
final≅-↓ n k1 m (long≅ {n₁} k l r .(n ↓ k1) .m defm defmf) =
  repeat-spaced-long-lemma n k1 ((S (k + n₁))) (S (k + n₁)) (≤-reflexive idp) l (((n₁ ↓ (1 + k)))) r defm

-- a helper trichotomy type
data _||_||_ (A : Type₀) (B : Type₀) (C : Type₀) : Type₀ where
  R1 : A -> A || B || C
  R2 : B -> A || B || C
  R3 : C -> A || B || C

-- a technical lemma about splitting Listℕs
lemma-l++2++r : (a b : ℕ) -> (l1 r1 l2 r2 : Listℕ) -> (l1 ++ r1 == l2 ++ a ∷ b ∷ r2)
                -> (Σ (Listℕ × Listℕ) (λ (rl2 , rr2) -> (r2 == rl2 ++ rr2) × (l1 == l2 ++ a ∷ b ∷ rl2) × (r1 == rr2))) || -- the case when both a ∷ b are in left
                   (Σ (Listℕ × Listℕ) (λ (ll2 , lr2) -> (l2 == ll2 ++ lr2) × (l1 == ll2) × (r1 == lr2 ++ a ∷ b ∷ r2))) || -- the case when both a ∷ b are in right
                   ((l1 == l2 ++ [ a ]) × (r1 == b ∷ r2)) -- the case when one a is in left, and b in right
lemma-l++2++r a b nil r1 l2 r2 p = R2 ((nil , l2) , (idp , (idp , p)))
lemma-l++2++r a b (x ∷ nil) r1 nil r2 p =
  let h = cut-tail p
  in  R3 ((cong [_] h) , (cut-head p))
lemma-l++2++r a b (x ∷ x₁ ∷ l1) r1 nil r2 p =
  let h1 = cut-tail p
      h2 = cut-tail (cut-head p)
  in  R1 ((l1 , r1) , (cut-head (cut-head (≡-sym p)) , (head+tail h1 (head+tail h2 idp)) , idp))
lemma-l++2++r a b (x ∷ l1) r1 (x₁ ∷ l2) r2 p with lemma-l++2++r a b l1 r1 l2 r2 (cut-head p)
... | R1 ((fst , snd) , fst₁ , fst₂ , snd₁) = R1 ((fst , snd) , (fst₁ , ((head+tail (cut-tail p) fst₂) , snd₁)))
... | R2 ((fst , snd) , fst₁ , fst₂ , snd₁) = R2 (((x₁ ∷ fst) , snd) , ((cong (λ e -> x₁ ∷ e) fst₁) , ((head+tail (cut-tail p) fst₂) , snd₁)))
... | R3 (fst , snd) = R3 (head+tail (cut-tail p) fst , snd)

-- a technical lemma about splitting Listℕs
lemma-l++1++r : (a : ℕ) -> (l1 r1 l2 r2 : Listℕ) -> (l1 ++ r1 == l2 ++ a ∷ r2)
                -> (Σ (Listℕ × Listℕ) (λ (rl2 , rr2) -> (r2 == rl2 ++ rr2) × (l1 == l2 ++ a ∷ rl2) × (r1 == rr2))) ⊔ -- the case when a is in left
                   (Σ (Listℕ × Listℕ) (λ (ll2 , lr2) -> (l2 == ll2 ++ lr2) × (l1 == ll2) × (r1 == lr2 ++ a ∷ r2))) -- the case when a is in right
lemma-l++1++r a nil r1 l2 r2 p = inr ((nil , l2) , (idp , (idp , p)))
lemma-l++1++r a (x ∷ l1) r1 nil r2 p = inl ((l1 , r1) , (! (cut-head p) , (head+tail (cut-tail p) idp , idp)))
lemma-l++1++r a (x ∷ l1) r1 (x₁ ∷ l2) r2 p with lemma-l++1++r a l1 r1 l2 r2 (cut-head p)
... | inl ((fst₁ , snd₁) , fst₂ , fst₃ , snd₂) = inl ((_ , _) , (fst₂ , (head+tail (cut-tail p) fst₃ , snd₂)))
... | inr ((fst₁ , snd₁) , fst₂ , fst₃ , snd₂) = inr ((_ , _) , (head+tail (cut-tail (! p)) fst₂ , (head+tail idp fst₃ , snd₂)))

last-↓ : (n k o : ℕ) -> (l : Listℕ) -> (n ↓ k == l ++ [ o ]) -> (n == o)
last-↓ n (S O) o nil p = cut-tail p
last-↓ n (S k) o (x ∷ l) p = last-↓ n k o l (cut-head p)

final≅-↓-↓ : (n k n1 k1 : ℕ) -> (m : Listℕ) -> (k + n < k1 + n1) -> ((n ↓ k) ++ (n1 ↓ k1)) ≅ m -> ⊥
final≅-↓-↓ n k n1 k1 m pkn (cancel≅ {n₁} l r .((n ↓ k) ++ (n1 ↓ k1)) .m defm defmf) with (lemma-l++2++r n₁ n₁ (n ↓ k) (n1 ↓ k1) l r defm)
final≅-↓-↓ n k n1 k1 m pkn (cancel≅ {n₁} l r .(n ↓ k ++ n1 ↓ k1) .m defm defmf) | R1 (x , fst₁ , fst₂ , snd₁) = 
    dec-long-lemma n k n₁ n₁ (≤-reflexive idp) l (fst x) fst₂
final≅-↓-↓ n k n1 k1 m pkn (cancel≅ {n₁} l r .(n ↓ k ++ n1 ↓ k1) .m defm defmf) | R2 (x , fst₁ , fst₂ , snd₁) = 
    dec-long-lemma n1 k1 n₁ n₁ (≤-reflexive idp) (snd x) r snd₁
final≅-↓-↓ n O n1 (S k1) m pkn (cancel≅ {n₁} nil r .(n ↓ O ++ n1 ↓ S k1) .m defm defmf) | R3 (() , snd₁)
final≅-↓-↓ n O n1 (S k1) m pkn (cancel≅ {n₁} (x ∷ l) r .(n ↓ O ++ n1 ↓ S k1) .m defm defmf) | R3 (() , snd₁)
final≅-↓-↓ n (S k) n1 (S k1) m pkn (cancel≅ {o} l r .(n ↓ S k ++ n1 ↓ S k1) .m defm defmf) | R3 (fst₁ , snd₁) = 
  let k1+n1=o = cut-tail snd₁
      n=o = last-↓ _ _ _ _ fst₁
      open ≤-Reasoning
      lemma =
        ≤begin
          S (S o)
        ≡⟨ ap (λ e -> S (S e)) (≡-sym n=o) ⟩ 
         S (S n) 
        ≤⟨ ≤-up2 (≤-up2 (≤-up-+ (≤-reflexive idp))) ⟩ 
          S (S (k + n))
        ≤⟨ pkn ⟩ 
          S (k1 + n1)
        ≡⟨ ap S k1+n1=o ⟩ 
          S o
        ≤∎
  in  ⊥-elim (1+n≰n lemma)
final≅-↓-↓ n k n1 k1 m pkn (swap≅ x l r .((n ↓ k) ++ (n1 ↓ k1)) .m defm defmf) with (lemma-l++2++r _ _ (n ↓ k) (n1 ↓ k1) l r defm)
... | R1 (q , fst₁ , fst₂ , snd₁) = incr-long-lemma n k _ _ x l (fst q) fst₂
... | R2 (q , fst₁ , fst₂ , snd₁) = incr-long-lemma n1 k1 _ _ x (snd q) r snd₁
final≅-↓-↓ n O n1 (S k1) m pkn (swap≅ x nil r .(n ↓ O ++ n1 ↓ S k1) .m defm defmf) | R3 (() , snd₁)
final≅-↓-↓ n O n1 (S k1) m pkn (swap≅ x (x₁ ∷ l) r .(n ↓ O ++ n1 ↓ S k1) .m defm defmf) | R3 (() , snd₁)
final≅-↓-↓ n (S k) n1 (S k1) m pkn (swap≅ {wn} {wk} x l r .(n ↓ S k ++ n1 ↓ S k1) .m defm defmf) | R3 (fst₁ , snd₁) = 
    let k1+n1=wk = cut-tail snd₁
        n=wn = last-↓ _ _ _ _ fst₁
        open ≤-Reasoning
        lemma =
          ≤begin
            S (S (S (S wk)))
          ≤⟨ ≤-up2 (≤-up2 x) ⟩
            S (S wn)
          ≡⟨ ap (λ e -> S (S e)) (≡-sym n=wn) ⟩ 
          S (S n)
          ≤⟨ ≤-up2 (≤-up2 (≤-up-+ (≤-reflexive idp))) ⟩ 
            S (S (k + n))
          ≤⟨ pkn ⟩ 
            S (k1 + n1)
          ≡⟨ ap S k1+n1=wk ⟩ 
            S wk
          ≤∎
  in  ⊥-elim (1+n≰n (≤-down (≤-down lemma)))
final≅-↓-↓ n k n1 k1 m pkn (long≅ k₁ l r .((n ↓ k) ++ (n1 ↓ k1)) .m defm defmf) = 
  repeat-↓-long-lemma n k n1 k1 _ (S k₁) pkn l r defm

open ≤-Reasoning

>>-⊥ : (n k : ℕ) -> (n ≤ k) -> (l l1 r1 : Listℕ) -> (n >> l) -> (l == l1 ++ k ∷ r1) -> ⊥
>>-⊥ n k pnk .(k₁ ∷ _) nil r1 (k₁ :⟨ x ⟩: w) defl = 
  let lemma =
            ≤begin
              S n
            ≤⟨ ≤-up2 pnk ⟩
              S k
            ≡⟨ ap S (cut-tail (! defl)) ⟩
              S k₁
            ≤⟨ x ⟩
              n
            ≤∎
  in 1+n≰n lemma
>>-⊥ n k pnk (x₁ ∷ l) (x ∷ l1) r1 (.x₁ :⟨ x₂ ⟩: w) defl = >>-⊥ n k pnk l l1 r1 w (cut-head defl)

tlm : {n : ℕ} -> (cl : Lehmer n) -> (k m rl : ℕ) -> (x : S rl ≤ S n) -> (l : Listℕ) -> (S (k + m) ≤ n ∸ S rl) -> (l ++ S (k + m) ∷ k + m ∷ m ↓ k == immersion (CanS cl {S rl} x)) -> ⊥
tlm {n} cl k m O x l pkmr p = 
  let 0<n = 
          ≤begin
            S O
          ≤⟨ ≤-up2 z≤n ⟩
            S (k + m)
          ≤⟨ pkmr ⟩
            n ∸ 1
          ≤⟨ ∸-anti-≤ {1} {0} {n} z≤n ⟩ 
            n
          ≤∎

      lemma2 = ++-assoc l (k + S m ∷ S m ↓ k) [ m ] ∙ ap (λ e → l ++ e) (++-↓ m (S k))
      lemma3 = cut-prefix (! p ∙ ! lemma2)
      lemma4 =
          ≤begin
            S n
          ≡⟨ ap S lemma3 ⟩
            S m
          ≤⟨ ≤-up2 (≤-up (≤-up-+ rrr)) ⟩
            S (S (k + m))
          ≤⟨ ≤-up2 pkmr ⟩
            S (n ∸ 1)
          ≡⟨ ! (∸-up {n} {0} 0<n) ⟩ 
            n
          ≤∎

  in  1+n≰n lemma4
tlm {n} cl O m (S rl) x l pkmr p = 
  let lemma1 = (++-assoc (immersion cl) (rl + S (n ∸ S rl) ∷ S (n ∸ S rl) ↓ rl) [ n ∸ S rl ])
      lemma2 = ap (λ e -> immersion cl ++ e) (++-↓ (n ∸ S rl) (S rl)) ∙ ! p ∙ ! (++-assoc l (S m ∷ nil) [ m ])
      lemma3 = cut-prefix (lemma1 ∙ lemma2)
      lemma4 = cut-last (lemma1 ∙ lemma2)

      lemma5 = 
            ≤begin
              S (n ∸ S (S rl))
            ≤⟨ ≤-up2 (∸-anti-≤ {S (S rl)} {S rl} {n} (≤-up rrr)) ⟩ 
              S (n ∸ S rl)
            ≡⟨ ap S lemma3 ⟩ 
              S m
            ≤⟨ pkmr ⟩
              n ∸ S (S rl)
            ≤∎
  in  1+n≰n lemma5
tlm {n} cl (S k) m (S rl) x l pkmr p = 
  let lemma1 = (++-assoc (immersion cl) (rl + S (n ∸ S rl) ∷ S (n ∸ S rl) ↓ rl) [ n ∸ S rl ])
      lemma2 = ap (λ e → l ++ e) (++-↓ m (S (S k)))
      lemma3 = ap (λ e -> immersion cl ++ e) (++-↓ (n ∸ S rl) (S rl)) ∙ ! p ∙ ! lemma2 ∙ ! (++-assoc l ((S k) + S m ∷ S m ↓ (S k)) [ m ])
      lemma4 = cut-prefix (lemma1 ∙ lemma3)
      lemma5 = cut-last (lemma1 ∙ lemma3)
      lemma6 = 
        ≤begin
          S (k + S m)
        ≡⟨ +-three-assoc {S k} {1} {m} ⟩ 
          S (S (k + m))
        ≤⟨ pkmr ⟩
          n ∸ S (S rl)
        ≤⟨ ∸-anti-≤ {S (S rl)} {S rl} {n} (s≤s (≤-up rrr)) ⟩
          n ∸ S rl
        ≤∎
  in  tlm cl k (S m) rl (≤-down x) l lemma6 (! lemma5 ∙ transport (λ e -> immersion cl ++ rl + e ∷ e ↓ rl == immersion cl ++ rl + n ∸ rl ∷ n ∸ rl ↓ rl) (∸-up x) idp)

immersion-long-lemma : {n : ℕ} -> (cl : Lehmer n) -> (k m : ℕ) -> (l r : Listℕ) -> (immersion cl == l ++ S (k + m) ∷ k + m ∷ (m ↓ k ++ S (k + m) ∷ (rev r))) -> ⊥
immersion-long-lemma {.0} CanZ k m nil r ()
immersion-long-lemma {.0} CanZ k m (x ∷ l) r ()
immersion-long-lemma {.(S _)} (CanS cl {O} x) k m l r dfm = immersion-long-lemma cl k m l r (! ++-unit ∙ dfm)
immersion-long-lemma {S n} (CanS cl {S O} x) k m l nil dfm = 
  let lemma2 = ! (++-assoc l (S (k + m) ∷ k + m ∷ (m ↓ k)) (S (k + m) ∷ nil))
      lemma3 = cut-prefix ((! lemma2 ∙ ! dfm))
      lemma4 = cut-last ((! lemma2 ∙ ! dfm))
      lemma6 = transport (λ e -> immersion cl ++ e == (l ++ S (k + m) ∷ k + m ∷ m ↓ k) ++ S (k + m) ∷ nil) (ap [_] lemma3) (ap (λ e -> e ++ [ S (k + m) ]) (! lemma4))
  in  >>-⊥ n (S (k + m)) (≤-reflexive (! lemma3)) (immersion cl) l (k + m ∷ (m ↓ k)) (immersion->> cl) (cut-last lemma6)
immersion-long-lemma {S n} (CanS cl {S (S rl)} x) k m l nil dfm =
  let lemma1 = ap (λ e -> immersion cl ++ e) (! (++-↓ (n ∸ S rl) (S rl)))
      lemma2 = ! (++-assoc l (S (k + m) ∷ k + m ∷ (m ↓ k)) (S (k + m) ∷ nil))
      lemma3 = cut-prefix ((! lemma2 ∙ ! dfm) ∙ lemma1  ∙ ! (++-assoc (immersion cl) (rl + S (n ∸ S rl) ∷ S (n ∸ S rl) ↓ rl) [ n ∸ S rl ]))
      lemma4 = cut-last ((! lemma2 ∙ ! dfm) ∙ lemma1  ∙ ! (++-assoc (immersion cl) (rl + S (n ∸ S rl) ∷ S (n ∸ S rl) ↓ rl) [ n ∸ S rl ]))
  in  tlm cl k m rl (≤-down x) l (≤-reflexive lemma3) (lemma4 ∙ ap (λ e -> immersion cl ++ rl + e ∷ e ↓ rl) (! (∸-up x)))
immersion-long-lemma {(S n)} (CanS cl {S rl} x) k m l (x₁ ∷ r) dfm = 
  let lemma1 = ap (λ e -> immersion cl ++ e) (! (++-↓ (n ∸ rl) rl))
      lemma2 = ! (++-assoc l (S (k + m) ∷ k + m ∷ (m ↓ k)) (S (k + m) ∷ (rev r ++ [ x₁ ]))) ∙ ! (++-assoc (l ++ S (k + m) ∷ k + m ∷ m ↓ k) (S (k + m) ∷ rev r) [ x₁ ])
      lemma3 = cut-prefix ((! lemma2 ∙ ! dfm) ∙ lemma1  ∙ ! (++-assoc (immersion cl) _ [ n ∸ rl ]))
      lemma4 = cut-last ((! lemma2 ∙ ! dfm) ∙ lemma1  ∙ ! (++-assoc (immersion cl) _ [ n ∸ rl ]))
      lemma5 = ++-assoc l (S (k + m) ∷ k + m ∷ m ↓ k) (S (k + m) ∷ rev r)
  in  immersion-long-lemma (CanS cl {rl} (≤-down x)) k m l r ((ap (λ e -> immersion cl ++ e ↓ rl) (∸-up x) ∙ ! lemma4) ∙ lemma5)

final≅-Lehmer : {n : ℕ} -> (cl : Lehmer n) -> (m mf : Listℕ) -> (defm : m == (immersion {n} cl)) -> m ≅ mf -> ⊥
final≅-Lehmer {O} CanZ nil mf defm p = empty-reduction p
final≅-Lehmer {S O} (CanS CanZ {O} x) nil mf defm p = empty-reduction p
final≅-Lehmer {S O} (CanS CanZ {S .0} (s≤s z≤n)) (x ∷ nil) mf defm p = one-reduction p
final≅-Lehmer {S (S n)} (CanS (CanS cl {r₁} x₁) {r₂} x₂) m mf defm (cancel≅ {n₁} l r .m .mf defm₁ defmf) 
  with (lemma-l++2++r n₁ n₁ ((immersion cl ++ S n ∸ r₁ ↓ r₁)) (S (S n) ∸ r₂ ↓ r₂) l r ((! defm) ∙ defm₁))
... | R1 ((fst₁ , snd₁) , fst₂ , fst₃ , snd₂) = final≅-Lehmer {S n} (CanS cl {r₁} x₁) _ _ idp (cancel≅ _ _ _ _ fst₃ idp)
... | R2 ((fst₁ , snd₁) , fst₂ , fst₃ , snd₂) = final≅-↓ (S (S n) ∸ r₂) r₂ _ (cancel≅ _ _ _ _ snd₂ idp)
final≅-Lehmer {S (S n)} (CanS (CanS cl {r₁} x₁) {S r₂} x₂) m mf defm (cancel≅ {n₁} l r .m .mf defm₁ defmf) | R3 (fst₁ , snd₁) = 
  >>-⊥ (S n) n₁ (≤-reflexive (! (plus-minus (≤-down2 x₂)) ∙ (cut-tail snd₁))) (immersion (CanS cl {r₁} x₁)) l nil (immersion->> (CanS cl {r₁} x₁)) fst₁
final≅-Lehmer {S (S n)} (CanS (CanS cl {r₁} x₁) {r₂} x₂) m mf defm (swap≅ {n₁} {k₁} ps l r .m .mf defm₁ defmf) 
  with (lemma-l++2++r n₁ k₁ ((immersion cl ++ S n ∸ r₁ ↓ r₁)) (S (S n) ∸ r₂ ↓ r₂) l r ((! defm) ∙ defm₁))
... | R1 ((fst₁ , snd₁) , fst₂ , fst₃ , snd₂) = final≅-Lehmer {S n} (CanS cl {r₁} x₁) _ _ idp (swap≅ ps _ _ _ _ fst₃ idp)
... | R2 ((fst₁ , snd₁) , fst₂ , fst₃ , snd₂) = final≅-↓ (S (S n) ∸ r₂) r₂ _ (swap≅ ps _ _ _ _ snd₂ idp)
final≅-Lehmer {S (S n)} (CanS (CanS cl {r₁} x₁) {S r₂} x₂) m mf defm (swap≅ {n₁} {k₁} ps l r .m .mf defm₁ defmf) | R3 (fst₁ , snd₁) =
  let lemma = 
          ≤begin
            S (S (S n))
          ≡⟨ ! (ap (λ e -> S (S e)) (plus-minus (≤-down2 x₂))) ⟩ 
            S (S (r₂ + S n ∸ r₂))
          ≡⟨ ap (λ e -> S (S e)) (cut-tail snd₁) ⟩
            S (S k₁)
          ≤⟨ ps ⟩
            n₁
          ≤∎
  in  >>-⊥ (S n) n₁ (≤-down (≤-down lemma)) (immersion (CanS cl {r₁} x₁)) l nil (immersion->> (CanS cl {r₁} x₁)) fst₁
final≅-Lehmer {S (S n)} (CanS (CanS cl {r₁} x₁) {r₂} x₂) m mf defm (long≅ {n₁} k l r .m .mf defm₁ defmf) = 
  let lemma = transport (λ e -> l ++ S (k + n₁) ∷ k + n₁ ∷ (n₁ ↓ k ++ S (k + n₁) ∷ e) == l ++ S (k + n₁) ∷ k + n₁ ∷ (n₁ ↓ k ++ S (k + n₁) ∷ rev (rev r))) (! rev-rev) idp
  in  immersion-long-lemma (CanS (CanS cl x₁) x₂) k n₁ l (rev r) ( (! defm) ∙ defm₁ ∙ lemma)

≡-↓ : (n k1 k2 : ℕ) -> (k1 ≤ n) -> (k2 ≤ n) -> ((n ↓ k1) == (n ↓ k2)) -> (k1 == k2)
≡-↓ n O O pk1 pk2 r = idp
≡-↓ n (S k1) (S k2) pk1 pk2 r = 
   let rec = ≡-↓ _ _ _ (≤-down pk1) (≤-down pk2) (cut-head r)
   in  cong S rec

≡-++↓ : (m1 m2 : Listℕ) -> (n k1 k2 : ℕ) -> (ml1 : n >> m1) -> (ml2 : n >> m2) -> (k1 ≤ S n) -> (k2 ≤ S n) -> (m1 ++ ((S n ∸ k1) ↓ k1) == m2 ++ ((S n ∸ k2) ↓ k2)) -> (k1 == k2) × (m1 == m2)
≡-++↓ nil nil n O O ml1 ml2 pk1 pk2 p = idp , idp
≡-++↓ nil nil O (S .0) (S .0) ml1 ml2 (s≤s z≤n) (s≤s z≤n) p = idp , idp
≡-++↓ nil nil (S n) (S k1) (S k2) ml1 ml2 pk1 pk2 p = 
  let rec-k , rec-l = ≡-++↓ nil nil n k1 k2 nil nil (≤-down2 pk1) (≤-down2 pk2) (cut-head p)
  in  (ap S rec-k) , idp
≡-++↓ nil (x ∷ m2) n (S k1) k2 ml1 (.x :⟨ x₁ ⟩: ml2) pk1 pk2 p = 
  let c = cut-tail p
  in  ⊥-elim (1+n≰n (≤-trans (≤-reflexive (ap S c)) (≤-trans x₁ (≤-reflexive (! (plus-minus (≤-down2 pk1)))))))
≡-++↓ (x ∷ m1) nil n k1 (S k2) (.x :⟨ x₁ ⟩: ml1) ml2 pk1 pk2 p = 
  let c = cut-tail p
  in  ⊥-elim (1+n≰n (≤-trans (≤-reflexive (ap S (! c))) ((≤-trans x₁ (≤-reflexive (! (plus-minus (≤-down2 pk2))))))))
≡-++↓ (x ∷ m1) (x₁ ∷ m2) n k1 k2 (.x :⟨ x₂ ⟩: ml1) (.x₁ :⟨ x₃ ⟩: ml2) pk1 pk2 p =
  let rec-k , rec-l = ≡-++↓ m1 m2 n k1 k2 ml1 ml2 pk1 pk2 (cut-head p)
      heads = cut-tail p
  in  rec-k , head+tail heads rec-l

≡immersion : {n : ℕ} -> (cl1 cl2 : Lehmer n) -> (immersion {n} cl1 == immersion {n} cl2) -> cl1 == cl2
≡immersion CanZ CanZ idp = idp
≡immersion {n} (CanS cl1 {r = r} x) (CanS cl2 {r = r₁} x₁) p = 
  let n>>cl1 = immersion->> cl1
      n>>cl2 = immersion->> cl2
      lemma-r , lemma-cl = ≡-++↓ _ _ _ _ _ n>>cl1 n>>cl2 x x₁ p
      rec = ≡immersion cl1 cl2 lemma-cl
  in lehmer-eta x x₁ rec lemma-r

only-one-canonical≅* : {n : ℕ} -> (cl1 cl2 : Lehmer n) -> (m1 m2 : Listℕ) -> (immersion {n} cl1 == m1) -> (immersion {n} cl2 == m2) -> (m1 ≅* m2)-> cl1 == cl2
only-one-canonical≅* cl1 cl2 m1 .m1 pm1 pm2 idp = ≡immersion _ _ (≡-trans pm1 (≡-sym pm2))
only-one-canonical≅* {n} cl1 cl2 m1 m2 pm1 pm2 (trans≅ x p) =
  let ss = transport (λ t → t ≅ _) (! pm1) x
  in  ⊥-elim (final≅-Lehmer cl1 (immersion {n} cl1) _ idp ss)

only-one-canonical↔ : {n : ℕ} -> (cl1 cl2 : Lehmer n) -> (m1 m2 : Listℕ) -> (immersion {n} cl1 == m1) -> (immersion {n} cl2 == m2) -> (m1 ↔ m2) -> cl1 == cl2
only-one-canonical↔ cl1 cl2 m1 .m1 pm1 pm2 (MC idp idp) = ≡immersion _ _ (≡-trans pm1 (≡-sym pm2))
only-one-canonical↔ {n} cl1 cl2 m1 m2 pm1 pm2 (MC idp (trans≅ x p2)) =
  let ss = transport (λ t → t ≅ _) (≡-sym pm2) x
  in  ⊥-elim (final≅-Lehmer cl2 _ _ idp ss)
only-one-canonical↔ {n} cl1 cl2 m1 m2 pm1 pm2 (MC (trans≅ x p1) p2) =
  let ss = transport (λ t → t ≅ _) (≡-sym pm1) x
  in  ⊥-elim (final≅-Lehmer cl1 _ _ idp ss)
