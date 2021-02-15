{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.Indexed.Equiv1Norm where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^

open import Pi+.UFin
open import Pi+.Extra

open import Pi+.Lehmer.Lehmer using (Lehmer)
open import Pi+.Lehmer.LehmerFinEquiv
open import Pi+.Coxeter.LehmerCoxeterEquiv
open import Pi+.Coxeter.Sn
open import Pi+.UFinLehmerEquiv

open import Pi+.Indexed.Equiv0Norm
open import Pi+.Indexed.Equiv1NormHelpers

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

postulate
    U^-is-singleton=idp-rewrite : {t : U^ n} → (U^-is-Singleton t t) ↦ idp -- U^-is-singleton=idp
    ℕ-S-is-inj-rewrite : {n : ℕ} -> (ℕ-S-is-inj n n idp) ↦ idp -- path in ℕ
    {-# REWRITE U^-is-singleton=idp-rewrite ℕ-S-is-inj-rewrite #-}

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
lehmer2lehmer {n} p = 
    ap immersion⁻¹ (idp ∙ (list2list (immersion p))) ∙ immersion⁻¹∘immersion p -- 

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

quoteNorm₁ : {n m : ℕ} → (pn : n == m) → (t₁ : U^ n) → (t₂ : U^ m) -> Aut (Fin n) → t₁ ⟷₁^ t₂
quoteNorm₁ {O} idp O O p = id⟷₁^
quoteNorm₁ {S n} {S m} q _ _ p =
    let step1 : Lehmer n
        step1 = –> Fin≃Lehmer p

        step2 = lehmer2normpi q step1
    in  step2

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
    let cancelNorm : normpi2lehmer {t₁ = (quoteNorm₀ (pFin _))} {t₂ = (quoteNorm₀ (pFin _))} (lehmer2normpi idp (–> Fin≃Lehmer p)) == (–> Fin≃Lehmer p)
        cancelNorm = lehmer2lehmer (–> Fin≃Lehmer p)

        cancelSn : <– Fin≃Lehmer (normpi2lehmer {t₁ = (quoteNorm₀ (pFin _))} {t₂ = (quoteNorm₀ (pFin _))} (lehmer2normpi idp (–> Fin≃Lehmer p))) == p
        cancelSn = ap  (<– Fin≃Lehmer) cancelNorm ∙ <–-inv-l Fin≃Lehmer p

    in  cancelSn