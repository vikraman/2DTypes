{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Indexed.Equiv1 where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxNorm as Pi^

open import Pi+.UFin
open import Pi+.Extra

open import Pi+.Lehmer.Lehmer using (Lehmer)
open import Pi+.Lehmer.LehmerFinEquiv
open import Pi+.Coxeter.LehmerCoxeterEquiv
open import Pi+.Coxeter.Sn
open import Pi+.UFinLehmerEquiv
open import Pi+.Indexed.Equiv0
open import Pi+.Indexed.PiCoxeter

open import lib.Basics
open import lib.types.Fin
open import lib.types.List
open import lib.types.BAut
open import lib.types.Nat
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct
open import lib.types.Sigma


private
    variable
        n m : ℕ    

eval^₁ : {t₁ : U n} {t₂ : U m} → (t₁ ⟷₁ t₂) → (eval^₀ t₁ ⟷₁^ eval^₀ t₂)
eval^₁ unite₊l = id⟷₁^
eval^₁ uniti₊l = id⟷₁^
eval^₁ (swap₊ {t₁ = t₁} {t₂ = t₂}) = ++^-swap (eval^₀ t₁) (eval^₀ t₂)
eval^₁ (assocl₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}) = ++^-assoc (eval^₀ t₁) (eval^₀ t₂) (eval^₀ t₃)
eval^₁ (assocr₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}) = !⟷₁^ (++^-assoc (eval^₀ t₁) (eval^₀ t₂) (eval^₀ t₃))
eval^₁ id⟷₁ = id⟷₁^
eval^₁ (c₁ ◎ c₂) = eval^₁ c₁ ◎^ eval^₁ c₂
eval^₁ (c₁ ⊕ c₂) = ++^-⊕ (eval^₁ c₁) (eval^₁ c₂)

lehmer2normpi : {t : U^ (S n)} → Lehmer n → t ⟷₁^ t
lehmer2normpi {n} cl = list2norm (immersion cl)

normpi2lehmer : {t : U^ (S n)} → t ⟷₁^ t → Lehmer n
normpi2lehmer {n} p = immersion⁻¹ (norm2list p)

normpi2normpi : {t : U^ (S n)} → (c : t ⟷₁^ t) →
    (lehmer2normpi {t = t} (normpi2lehmer c)) ⟷₂^ c
normpi2normpi {n} c =
    let lemma : immersion (immersion⁻¹ (norm2list c)) ≈ (norm2list c)
        lemma = immersion∘immersion⁻¹ (norm2list c)
        
        tt = trans⟷₂^ (piRespectsCox  _ _ lemma) (norm2norm c)
    in  trans⟷₂^ tt (trans⟷₂^ (id⟷₂^ ⊡^ big-id₊⟷₂id⟷₁ (!⟷₁^ c)) idr◎l^)

lehmer2lehmer : {n : ℕ} → (p : Lehmer n) → normpi2lehmer (lehmer2normpi p) == p
lehmer2lehmer {n} p = ap immersion⁻¹ (list2list (immersion p)) ∙ immersion⁻¹∘immersion p

evalNorm₁ : {t : U^ n} → (c : t ⟷₁^ t) → Aut (Fin n)
evalNorm₁ {O} {O} c = ide _ -- zero case
evalNorm₁ {S n} c =
    let step1 : Lehmer n
        step1 = normpi2lehmer c

        step2 : Aut (Fin (S n))
        step2 = <– Fin≃Lehmer step1

    in  step2

eval₁ : {t : U n} → (c : t ⟷₁ t) → Aut (Fin n)
eval₁ = evalNorm₁ ∘ eval^₁

quoteNorm₁ : (t : U^ n) -> Aut (Fin n) → t ⟷₁^ t
quoteNorm₁ {O} _ p = id⟷₁^
quoteNorm₁ {S n} _ p =
    let step1 : Lehmer n
        step1 = –> Fin≃Lehmer p

        step2 = lehmer2normpi step1
    in  step2

quote₁ : Aut (Fin n) → (quote₀ (pFin n) ⟷₁ quote₀ (pFin n))
quote₁ e = quote^₁ (quoteNorm₁ _ e)

quote-evalNorm₁ : {n : ℕ} {t : U^ n} → (c : t ⟷₁^ t) → quoteNorm₁ t (evalNorm₁ c) ⟷₂^ c
quote-evalNorm₁ {O} {O} p = !⟷₂^ (c₊⟷₂id⟷₁ p)
quote-evalNorm₁ {S n} p =
    let cancelSn : –> Fin≃Lehmer (<– Fin≃Lehmer (normpi2lehmer p)) == normpi2lehmer p
        cancelSn = <–-inv-r Fin≃Lehmer (normpi2lehmer p)

        cancelNorm : lehmer2normpi (–> Fin≃Lehmer (<– Fin≃Lehmer (normpi2lehmer p))) ⟷₂^ p
        cancelNorm = transport (λ e -> lehmer2normpi e ⟷₂^ p) (! cancelSn) (normpi2normpi p)

    in  cancelNorm

eval-quoteNorm₁ : {n : ℕ} → (p : Aut (Fin n)) → evalNorm₁ (quoteNorm₁ (i^ _) p) == p
eval-quoteNorm₁ {O} p = contr-has-all-paths {{Aut-FinO-level}} _ _
eval-quoteNorm₁ {S n} p =
    let cancelNorm : normpi2lehmer (lehmer2normpi (–> Fin≃Lehmer p)) == (–> Fin≃Lehmer p)
        cancelNorm = lehmer2lehmer (–> Fin≃Lehmer p)

        cancelSn : <– Fin≃Lehmer (normpi2lehmer (lehmer2normpi (–> Fin≃Lehmer p))) == p
        cancelSn = ap  (<– Fin≃Lehmer) cancelNorm ∙ <–-inv-l Fin≃Lehmer p

    in  cancelSn

denorm : {t₁ : U n} {t₂ : U m} → (c : t₁ ⟷₁ t₂) → quote^₀ (eval^₀ t₁) ⟷₁ quote^₀ (eval^₀ t₂)
denorm {t₁ = t₁} {t₂ = t₂} c = (quote-eval^₀ t₁ ◎ c ◎ !⟷₁ (quote-eval^₀ t₂))

norm : {t₁ : U^ n} {t₂ : U^ m} → (c : t₁ ⟷₁^ t₂) → eval^₀ (quote^₀ t₁) ⟷₁^ eval^₀ (quote^₀ t₂)
norm {t₁ = t₁} {t₂ = t₂} c = (eval-quote^₀ t₁ ◎^ c ◎^ !⟷₁^ (eval-quote^₀ t₂)) -- 

-- postulate
--     denorm∘norm : {X Y : U n} → (c : X ⟷₁ Y) → norm (denorm c) ⟷₂ c
--     norm∘denorm : {X Y : U^ n} → (c : X ⟷₁^ Y) → denorm (norm c) ⟷₂^ c

-- postulate
--     ap-id-rewrite : {t : U^ n} → (⊕^ (id⟷₁^ {t = t})) ↦ (id⟷₁^ {t = I+ t})
--     unitl-rewrite : {t₁ : U^ n} {t₂ : U^ m} {c : t₁ ⟷₁^ t₂} → (id⟷₁^ ◎^ c) ↦ c
--     unitr-rewrite : {t₁ : U^ n} {t₂ : U^ m} {c : t₁ ⟷₁^ t₂} → (c ◎^ id⟷₁^) ↦ c
--     {-# REWRITE ap-id-rewrite unitl-rewrite unitr-rewrite #-}
 

eval-quote^₁ : {t₁ : U^ n} {t₂ : U^ m} → (c : t₁ ⟷₁^ t₂) → eval^₁ (quote^₁ c) ⟷₂^ norm c
eval-quote^₁ (swap₊^ {t = t}) = {!   !}
    -- let cc = eval-quote^₀ t
    -- in  !⟷₂^ ( -- ) -- (swapl₊⟷₂^ {c = {! id⟷₁^  !}})
    --     (⊕^ ⊕^ cc) ◎^ (swap₊^ ◎^ ⊕^ (⊕^ (!⟷₁^ cc))) ⟷₂^⟨ _⊡^_ {c₁ = (⊕^ ⊕^ cc)} {c₂ = _} {c₃ = (⊕^ ⊕^ cc)} {c₄ = ((⊕^ (⊕^ !⟷₁^ cc)) ◎^ swap₊^)} {!   !}  {! swapl₊⟷₂^ !} ⟩
    --     {!   !} ⟷₂^⟨ {!   !} ⟩ -- (⊕^ ⊕^ cc) ◎^ ((⊕^ (⊕^ !⟷₁^ cc)) ◎^ swap₊^) ,, assoc◎l^
    --     ((⊕^ ⊕^ cc) ◎^ (⊕^ (⊕^ !⟷₁^ (cc)))) ◎^ swap₊^ ⟷₂^⟨ hom◎⊕⟷₂^ ⊡^ id⟷₂^ ⟩
    --     (⊕^ ((⊕^ cc) ◎^ (⊕^ !⟷₁^ (cc)))) ◎^ swap₊^ ⟷₂^⟨ (resp⊕⟷₂ hom◎⊕⟷₂^) ⊡^ id⟷₂^ ⟩
    --     (⊕^ (⊕^ ((cc) ◎^ (!⟷₁^ (cc))))) ◎^ swap₊^ ⟷₂^⟨ (resp⊕⟷₂ (resp⊕⟷₂ linv◎l^)) ⊡^ id⟷₂^ ⟩
    --     (⊕^ (⊕^ (id⟷₁^))) ◎^ swap₊^ ⟷₂^⟨ id⟷₂^ ⟩
    --     swap₊^ ⟷₂^∎)
eval-quote^₁ {n = n} {t₁ = t₁} id⟷₁^ = {!   !} -- !⟷₂^ (linv◎l^ {n} {t₁ = eval^₀ (quote^₀ t₁)} {t₂ = t₁} {c = eval-quote^₀ _})
eval-quote^₁ (c ◎^ c₁) = {!   !}
eval-quote^₁ (⊕^ c) = {!   !}

quote-eval^₁ : {t₁ : U n} {t₂ : U m} → (c : t₁ ⟷₁ t₂) → quote^₁ (eval^₁ c) ⟷₂ denorm c
quote-eval^₁ unite₊l = {!   !}
quote-eval^₁ uniti₊l = {!   !}
quote-eval^₁ swap₊ = {!   !}
quote-eval^₁ assocl₊ = {!   !}
quote-eval^₁ assocr₊ = {!   !}
quote-eval^₁ id⟷₁ = {!   !}
quote-eval^₁ (c ◎ c₁) = {!   !}
quote-eval^₁ (c ⊕ c₁) = {!   !}

-- evalNorm₂ : {t₁ : U^ n} {t₂ : U^ m} {c₁ c₂ : t₁ ⟷₁^ t₂} → c₁ ⟷₂^ c₂ → evalNorm₁ c₁ == evalNorm₁ c₂
-- evalNorm₂ α = {! α !}

eval-quote₁ : (e : Aut (Fin n)) → (eval₁ (quote₁ e)) == e
eval-quote₁ {n} e = 
    let l1 = eval-quoteNorm₁ e
        l2 = eval-quote^₁ (quoteNorm₁ (i^ n) e)
    in  {!   !} ∙ l1

quote-eval₁ : {t : U n} → (c : t ⟷₁ t) → (quote₁ (eval₁ c)) ⟷₂ (quote-eval₀ t ◎ c ◎ !⟷₁ (quote-eval₀ t))
quote-eval₁ e = {!   !}

-- Have:
--     eval-quote^₁ : {t₁ : U^ n} {t₂ : U^ m} → (c : t₁ ⟷₁^ t₂) → eval^₁ (quote^₁ c) ⟷₂^ norm c
--     eval-quoteNorm₁ : {n : ℕ} → (p : Aut (Fin n)) → evalNorm₁ (quoteNorm₁ (i^ _) p) == p

-- Goal:
--     eval-quote₁ : (e : Aut (Fin n)) → (eval₁ (quote₁ e)) == e
