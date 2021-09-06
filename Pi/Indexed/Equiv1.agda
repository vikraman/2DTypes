{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi.Indexed.Equiv1 where

open import Pi.Indexed.Syntax as Pi
open import Pi.Indexed.SyntaxHat as Pi^

open import Pi.Common.FinHelpers

open import Pi.UFin
open import Pi.Extra
open import Pi.Misc using (transport2)

open import Pi.Indexed.Equiv0Norm
open import Pi.Indexed.Equiv0Hat
open import Pi.Indexed.Equiv0
open import Pi.Indexed.Equiv1Norm
open import Pi.Indexed.Equiv1Hat
open import Pi.Indexed.Equiv2Norm
open import Pi.Indexed.Equiv2Hat

open import Pi.Indexed.Equiv1NormHelpers
open import Pi.Lehmer.Lehmer2FinEquiv
open import Pi.Coxeter.Lehmer2CoxeterEquiv

open import lib.Basics
open import lib.types.Fin
open import lib.types.List
open import lib.types.BAut
open import lib.types.Nat as N
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct
open import lib.types.Sigma


private
    variable
        n m : ℕ

eval₁ : {t₁ : U n} {t₂ : U m} → (c : t₁ ⟷₁ t₂) → Aut (Fin n)
eval₁ = evalNorm₁ ∘ eval^₁

quote₁ : {t₁ : U n} {t₂ : U m} → (p : n == m) → Aut (Fin n) → (t₁ ⟷₁ t₂)
quote₁ {t₁ = t₁} {t₂ = t₂} p e =
    let c = quote^₁ {n = eval^₀ t₁} {m = eval^₀ t₂} (quoteNorm₁ p e)
    in  denorm← c


id-⊕-== : (pi^2list (⊕^ (id⟷₁^ {n = n}))) == nil
id-⊕-== {O} = idp
id-⊕-== {S n} = idp

pi^2list-nil : pi^2list (⊕^ eval^₁ (quote-eval^₀ (quote^₀ n))) == nil
pi^2list-nil {O} = idp
pi^2list-nil {S n}
  rewrite (ℕ-p (+-assoc 1 0 n))
  rewrite (ℕ-p (+-unit-r 0))
  rewrite (ℕ-p (+-unit-r 1))
  rewrite (ℕ-p (+-assoc 0 0 1))
  rewrite (id-⊕-== {n = n}) = ap (map S⟨_⟩) ((ap (_++ nil) (++-unit-r _) ∙ ++-unit-r _) ∙ pi^2list-nil {n})

-- second proof, much simpler, but more code duplication
pi^2list-!-nil : pi^2list (⊕^ eval^₁ (!⟷₁ (quote-eval^₀ (quote^₀ n)))) == nil
pi^2list-!-nil {O} = idp
pi^2list-!-nil {S n}
  rewrite (ℕ-p (+-assoc 1 0 n))
  rewrite (ℕ-p (+-unit-r 0))
  rewrite (ℕ-p (+-unit-r 1))
  rewrite (ℕ-p (+-assoc 0 0 1))
  rewrite (id-⊕-== {n = n}) = ap (map S⟨_⟩) ((ap (_++ nil) (++-unit-r _) ∙ ++-unit-r _) ∙ pi^2list-!-nil {n})

-- second possible proof of pi^2list-!-nil with a few things left out
-- uses unfinished stuff from Equiv1NormHelpers.agda

-- pi^2list-!-nil' : pi^2list (⊕^ eval^₁ (!⟷₁ (quote-eval^₀ (quote^₀ n)))) == nil
-- pi^2list-!-nil' {n} =
--   ap (λ x → pi^2list (⊕^ x)) (eval^₁-! (quote-eval^₀ (quote^₀ n))) ∙
--   pi^2list-! (⊕^ (eval^₁ (quote-eval^₀ (quote^₀ n)))) ∙
--   transport (λ e → transport (λ k → List (Fin k)) e (reverse (pi^2list (⊕^ eval^₁ (quote-eval^₀ (quote^₀ n))))) == nil) (ℕ-p idp) (ap reverse pi^2list-nil)


eval-quote₁ : (e : Aut (Fin n)) → (eval₁ {t₁ = (quote₀ (pFin _))} {t₂ = (quote₀ (pFin _))} (quote₁ idp e)) == e
eval-quote₁ {O} e = contr-has-all-paths {{Aut-FinO-level}} _ _
eval-quote₁ {S n} e
  with evalNorm₂ (eval-quote^₁ (quoteNorm₁ idp e))
  with ⟷₁-eq-size (quote^₁ (list2pi^ (immersion (–> Fin≃Lehmer e))))
... | q | r
  rewrite (ℕ-p (+-assoc 1 0 n))
  rewrite (ℕ-p (+-unit-r 0))
  rewrite (ℕ-p (+-unit-r 1))
  rewrite (ℕ-p (+-assoc 0 0 1))
  rewrite (id-⊕-== {n = n})
  rewrite (pi^2list-nil {n = n})
  rewrite (pi^2list-!-nil {n = n}) =
    let s = eval-quoteNorm₁ e
    in  (ap ((<– Fin≃Lehmer) ∘ immersion⁻¹) (++-unit-r _)) ∙ q ∙ s

postulate
    eq-size-rewrite : {t₁ : U n} {t₂ : U m} {c : t₁ ⟷₁ t₂} → (⟷₁^-eq-size (eval^₁ c)) ↦ (⟷₁-eq-size c) -- because proof of == in ℕ
    {-# REWRITE eq-size-rewrite #-}

quote-eval²₀ : (t : U n) → quote-eval^₀ (quote^₀ (eval^₀ t)) ⟷₂ id⟷₁
quote-eval²₀ {O} t = id⟷₂
quote-eval²₀ {S n} t =
  let rec = quote-eval²₀ {n} (quote₀ (pFin _))
  in  _ ⟷₂⟨ id⟷₂ ⊡ resp⊕⟷₂ id⟷₂ rec ⟩
      _ ⟷₂⟨ TODO! ⟩ -- Goal: (((id⟷₁ ⊕ uniti₊l) ◎ assocl₊) ◎ unite₊r ⊕ id⟷₁) ⟷₂ id⟷₁
      _ ⟷₂∎

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
