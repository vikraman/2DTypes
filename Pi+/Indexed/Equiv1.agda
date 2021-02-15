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


denorm : {t₁ : U n} {t₂ : U m} → (c : t₁ ⟷₁ t₂) → quote^₀ (eval^₀ t₁) ⟷₁ quote^₀ (eval^₀ t₂)
denorm {t₁ = t₁} {t₂ = t₂} c = (quote-eval^₀ t₁ ◎ c ◎ !⟷₁ (quote-eval^₀ t₂))

denorm← : {t₁ : U n} {t₂ : U m} → (c : quote^₀ (eval^₀ t₁) ⟷₁ quote^₀ (eval^₀ t₂)) → t₁ ⟷₁ t₂
denorm← {t₁ = t₁} {t₂ = t₂} c = (!⟷₁ (quote-eval^₀ t₁)) ◎ c ◎ (quote-eval^₀ t₂)

norm : {t₁ : U^ n} {t₂ : U^ m} → (c : t₁ ⟷₁^ t₂) → eval^₀ (quote^₀ t₁) ⟷₁^ eval^₀ (quote^₀ t₂)
norm {t₁ = t₁} {t₂ = t₂} c = (eval-quote^₀ t₁ ◎^ c ◎^ !⟷₁^ (eval-quote^₀ t₂)) -- 


eval^₁ : {t₁ : U n} {t₂ : U m} → (t₁ ⟷₁ t₂) → (eval^₀ t₁ ⟷₁^ eval^₀ t₂)
eval^₁ unite₊l = id⟷₁^
eval^₁ uniti₊l = id⟷₁^
eval^₁ (swap₊ {t₁ = t₁} {t₂ = t₂}) = ++^-swap (eval^₀ t₁) (eval^₀ t₂)
eval^₁ (assocl₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}) = ++^-assoc (eval^₀ t₁) (eval^₀ t₂) (eval^₀ t₃)
eval^₁ (assocr₊ {t₁ = t₁} {t₂ = t₂} {t₃ = t₃}) = !⟷₁^ (++^-assoc (eval^₀ t₁) (eval^₀ t₂) (eval^₀ t₃))
eval^₁ id⟷₁ = id⟷₁^
eval^₁ (c₁ ◎ c₂) = eval^₁ c₁ ◎^ eval^₁ c₂
eval^₁ (c₁ ⊕ c₂) = ++^-⊕ (eval^₁ c₁) (eval^₁ c₂)

lehmer2normpi : {t₁ : U^ (S n)} {t₂ : U^ (S m)} → (S n == S m) → Lehmer n → t₁ ⟷₁^ t₂
lehmer2normpi p cl = list2normI (ℕ-S-is-inj _ _ p) (immersion cl)

normpi2lehmer : {t₁ : U^ (S n)} {t₂ : U^ (S m)} → t₁ ⟷₁^ t₂ → Lehmer n
normpi2lehmer {n} p = immersion⁻¹ (norm2list p)

normpi2normpi : {t₁ : U^ (S n)} {t₂ : U^ (S m)} → (c : t₁ ⟷₁^ t₂) →
    (lehmer2normpi {t₁ = t₁} {t₂ = t₂} (⟷₁^-eq-size c) (normpi2lehmer c)) ⟷₂^ c
normpi2normpi {n} c =
    let lemma : immersion (immersion⁻¹ (norm2list c)) ≈ (norm2list c)
        lemma = immersion∘immersion⁻¹ (norm2list c)
    in  trans⟷₂^ (piRespectsCox (ℕ-S-is-inj _ _ (⟷₁^-eq-size c)) _ _ lemma) (norm2norm c)

lehmer2lehmer : {n : ℕ} → (p : Lehmer n) → normpi2lehmer (lehmer2normpi {t₁ = (quoteNorm₀ (pFin _))} {t₂ = (quoteNorm₀ (pFin _))} idp p) == p
lehmer2lehmer {n} p rewrite (lemma4 (quoteNorm₀ (pFin n))) = 
    ap immersion⁻¹ ({!   !} ∙ (list2list (immersion p))) ∙ immersion⁻¹∘immersion p -- 

evalNorm₁ : {t₁ : U^ n} {t₂ : U^ m} → (c : t₁ ⟷₁^ t₂) → Aut (Fin n)
evalNorm₁ {O} {O} c = ide _ -- zero case
evalNorm₁ {S n} {S m} c =
    let step1 : Lehmer n
        step1 = normpi2lehmer c

        step2 : Aut (Fin (S n))
        step2 = <– Fin≃Lehmer step1

    in  step2
evalNorm₁ {S n} {O} c with (⟷₁^-eq-size c)
... | ()
evalNorm₁ {O} {S m} c with (⟷₁^-eq-size c)
... | ()


eval₁ : {t₁ : U n} {t₂ : U m} → (c : t₁ ⟷₁ t₂) → Aut (Fin n)
eval₁ = evalNorm₁ ∘ eval^₁

quoteNorm₁ : {n m : ℕ} → (pn : n == m) → (t₁ : U^ n) → (t₂ : U^ m) -> Aut (Fin n) → t₁ ⟷₁^ t₂
quoteNorm₁ {O} idp O O p = id⟷₁^
quoteNorm₁ {S n} {S m} q _ _ p =
    let step1 : Lehmer n
        step1 = –> Fin≃Lehmer p

        step2 = lehmer2normpi q step1
    in  step2

quote₁ : {t₁ : U n} {t₂ : U m} → (p : n == m) → Aut (Fin n) → (t₁ ⟷₁ t₂)
quote₁ {t₁ = t₁} {t₂ = t₂} p e = 
    let c = quote^₁ {t₁ = eval^₀ t₁} {t₂ = eval^₀ t₂} (quoteNorm₁ p _ _ e)
    in  denorm← c

quote-evalNorm₁ : {n m : ℕ} {t₁ : U^ n} {t₂ : U^ m} → (c : t₁ ⟷₁^ t₂) → quoteNorm₁ (⟷₁^-eq-size c) t₁ t₂ (evalNorm₁ c) ⟷₂^ c
quote-evalNorm₁ {O} {O} {O} {O} c = trans⟷₂^ (c₊⟷₂id⟷₁ _) (!⟷₂^ (c₊⟷₂id⟷₁ c))
quote-evalNorm₁ {S n} {S m} p =
    let cancelSn : –> Fin≃Lehmer (<– Fin≃Lehmer (normpi2lehmer p)) == normpi2lehmer p
        cancelSn = <–-inv-r Fin≃Lehmer (normpi2lehmer p)

        cancelNorm : lehmer2normpi (⟷₁^-eq-size p) (–> Fin≃Lehmer (<– Fin≃Lehmer (normpi2lehmer p))) ⟷₂^ p
        cancelNorm = transport (λ e -> lehmer2normpi (⟷₁^-eq-size p) e ⟷₂^ p) (! cancelSn) (normpi2normpi p)

    in  cancelNorm
quote-evalNorm₁ {O} {S m} c with (⟷₁^-eq-size c)
... | ()
quote-evalNorm₁ {S n} {O} c with (⟷₁^-eq-size c)
... | ()

eval-quoteNorm₁ : {n : ℕ} → (p : Aut (Fin n)) → evalNorm₁ (quoteNorm₁ idp (quoteNorm₀ (pFin _)) (quoteNorm₀ (pFin _)) p) == p
eval-quoteNorm₁ {O} p = contr-has-all-paths {{Aut-FinO-level}} _ _
eval-quoteNorm₁ {S n} p =
    let cancelNorm : normpi2lehmer (lehmer2normpi idp (–> Fin≃Lehmer p)) == (–> Fin≃Lehmer p)
        cancelNorm = lehmer2lehmer (–> Fin≃Lehmer p)

        cancelSn : <– Fin≃Lehmer (normpi2lehmer (lehmer2normpi idp (–> Fin≃Lehmer p))) == p
        cancelSn = ap  (<– Fin≃Lehmer) cancelNorm ∙ <–-inv-l Fin≃Lehmer p

    in  cancelSn

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

evalNorm₂ : {t₁ : U^ n} {t₂ : U^ m} {c₁ c₂ : t₁ ⟷₁^ t₂} → c₁ ⟷₂^ c₂ → evalNorm₁ c₁ == evalNorm₁ c₂
evalNorm₂ {O} α = {!   !}
evalNorm₂ {S n} assoc◎l^ = {!   !}
evalNorm₂ {S n} assoc◎r^ = {!   !}
evalNorm₂ {S n} idl◎l^ = {!   !}
evalNorm₂ {S n} idl◎r^ = {!   !}
evalNorm₂ {S n} idr◎l^ = {!   !}
evalNorm₂ {S n} idr◎r^ = {!   !}
evalNorm₂ {S n} linv◎l^ = {!   !}
evalNorm₂ {S n} linv◎r^ = {!   !}
evalNorm₂ {S n} rinv◎l^ = {!   !}
evalNorm₂ {S n} rinv◎r^ = {!   !}
evalNorm₂ {S n} id⟷₂^ = {!   !}
evalNorm₂ {S n} (trans⟷₂^ α α₁) = {!   !}
evalNorm₂ {S n} (α ⊡^ α₁) = {!   !}
evalNorm₂ {S n} ⊕id⟷₁⟷₂^ = {!   !}
evalNorm₂ {S n} !⊕id⟷₁⟷₂^ = {!   !}
evalNorm₂ {S n} hom◎⊕⟷₂^ = {!   !}
evalNorm₂ {S n} (resp⊕⟷₂ α) = {!   !}
evalNorm₂ {S O} hom⊕◎⟷₂^ = {!   !}
evalNorm₂ {S (S n)} hom⊕◎⟷₂^ = {!   !}
evalNorm₂ {S .(S _)} swapr₊⟷₂^ = {!   !}
evalNorm₂ {S .(S _)} swapl₊⟷₂^ = {!   !}

eval^₂ : {t₁ : U n} {t₂ : U m} {c₁ c₂ : t₁ ⟷₁ t₂} → c₁ ⟷₂ c₂ → eval^₁ c₁ ⟷₂^ eval^₁ c₂
eval^₂ α = {!   !}

quote^₂ : {t₁ : U^ n} {t₂ : U^ m} {c₁ c₂ : t₁ ⟷₁^ t₂} → c₁ ⟷₂^ c₂ → quote^₁ c₁ ⟷₂ quote^₁ c₂
quote^₂ α = {!   !}

eval-quote₁ : (e : Aut (Fin n)) → (eval₁ {t₁ = (quote₀ (pFin _))} {t₂ = (quote₀ (pFin _))} (quote₁ idp e)) == e
eval-quote₁ {n} e = 
    let l1 = eval-quoteNorm₁ e
        l2 = eval-quote^₁ (quoteNorm₁ idp (quoteNorm₀ (pFin _)) (quoteNorm₀ (pFin _)) e)
        l3 = evalNorm₂ {n} {n} {_} {_} {_} {_} l2
    in  ({!   !} ∙ l3 ∙ {!   !}) ∙ l1 -- (l3 ∙ {!   !}) ∙ l1

postulate
    eval-quote₀-rewrite : {t : U^ n} → (eval^₀ (quote^₀ t)) ↦ t -- because eval-quote^==₀
    eq-size-rewrite : {t₁ : U n} {t₂ : U m} {c : t₁ ⟷₁ t₂} → (⟷₁^-eq-size (eval^₁ c)) ↦ (⟷₁-eq-size c) -- because proof of == in ℕ
    {-# REWRITE eval-quote₀-rewrite eq-size-rewrite #-}

quote-eval²₀ : (t : U n) → quote-eval^₀ (quote^₀ (eval^₀ t)) ⟷₂ id⟷₁
quote-eval²₀ O = id⟷₂
quote-eval²₀ I = {!   !}
quote-eval²₀ (t U.+ t₁) = {!   !}

quote-eval₁ : {t₁ : U n} {t₂ : U m} → (c : t₁ ⟷₁ t₂) → (quote₁ (⟷₁-eq-size c) (eval₁ c)) ⟷₂ denorm c
quote-eval₁ {t₁ = t₁} {t₂ = t₂} c = 
    let l1 = quote-eval^₁ c
        l2 = quote^₂ (quote-evalNorm₁ (eval^₁ c))
    in    _ 
        ⟷₂⟨ id⟷₂ ⊡ (l2 ⊡ id⟷₂) ⟩
          _
        ⟷₂⟨ !⟷₁⟷₂ (quote-eval²₀ t₁) ⊡ (id⟷₂ ⊡ quote-eval²₀ t₂) ⟩
          _
        ⟷₂⟨ id⟷₂ ⊡ idr◎l ⟩
          _
        ⟷₂⟨ idl◎l ⟩
          quote^₁ (eval^₁ c) 
        ⟷₂⟨ l1 ⟩
          denorm c 
        ⟷₂∎