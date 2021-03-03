{-# OPTIONS --without-K --exact-split --rewriting #-}

module Pi+.Indexed.Equiv1 where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxHat as Pi^

open import Pi+.Common.FinHelpers

open import Pi+.UFin
open import Pi+.Extra
open import Pi+.Misc using (transport2)

open import Pi+.Indexed.Equiv0Norm
open import Pi+.Indexed.Equiv0Hat
open import Pi+.Indexed.Equiv0
open import Pi+.Indexed.Equiv1Norm
open import Pi+.Indexed.Equiv1Hat
open import Pi+.Indexed.Equiv2Norm
open import Pi+.Indexed.Equiv2Hat

open import Pi+.Indexed.Equiv1NormHelpers
open import Pi+.Lehmer.LehmerFinEquiv
open import Pi+.Coxeter.LehmerCoxeterEquiv

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

import Pi+.Coxeter.LehmerCoxeterEquiv
import Pi+.Lehmer.LehmerFinEquiv

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

module _ where
  -- second possible proof of pi^2list-!-nil with a few TODOs
  -- but if we won't need these lemmas, then we can just delete
  -- the whole submodule below
  ++^-id-! : (p : n == m) → ++^-id p == !⟷₁^ (++^-id (! p))
  ++^-id-! idp = idp

  ++^-⊕-id : (c : n ⟷₁^ m) → ++^-⊕ c id⟷₁^ ⟷₂^ transport2 (λ n' m' → n' ⟷₁^ m') (! (+-unit-r n)) (! (+-unit-r m)) c
  ++^-⊕-id c = TODO

  ++^-⊕-! : {n m o p : ℕ} → (c₁ : n ⟷₁^ m) → (c₂ : o ⟷₁^ p) → ++^-⊕ (!⟷₁^ c₁) (!⟷₁^ c₂) == !⟷₁^ (++^-⊕ c₁ c₂)
  ++^-⊕-! {n} swap₊^ c₂ with (⟷₁^-eq-size (++^-⊕ (id⟷₁^ {n = n}) (!⟷₁^ c₂)))
  ... | q =  TODO
  ++^-⊕-! {O} id⟷₁^ c₂ = idp
  ++^-⊕-! {S n} id⟷₁^ c₂ = ap ⊕^_ (++^-⊕-! {n} id⟷₁^ c₂)
  ++^-⊕-! (c₁ ◎^ c₂) c₃ = 
    let r₁ = ++^-⊕-! c₁ id⟷₁^
        r₂ = ++^-⊕-! c₂ c₃
    in  ap2 _◎^_ r₂ r₁ ∙ TODO
  ++^-⊕-! (⊕^ c₁) c₂ = ap ⊕^_ (++^-⊕-! c₁ c₂)

  ++^-swap-! : {n m : ℕ} → ++^-swap m n == !⟷₁^ (++^-swap n m)
  ++^-swap-! {n} {m} = TODO

  eval^₁-! : {t₁ : U n} → {t₂ : U m} → (c : t₁ ⟷₁ t₂) → eval^₁ (!⟷₁ c) == !⟷₁^ (eval^₁ c)
  eval^₁-! unite₊l = idp
  eval^₁-! uniti₊l = idp
  eval^₁-! (swap₊ {n} {_} {m} {_}) = ++^-swap-! {n} {m}
  eval^₁-! assocl₊ = ++^-id-! _
  eval^₁-! assocr₊ = ++^-id-! _ ∙ ap (λ x → !⟷₁^ (++^-id x)) (!-! _)
  eval^₁-! id⟷₁ = idp
  eval^₁-! (c₁ ◎ c₂) = 
    let r₁ = eval^₁-! c₁
        r₂ = eval^₁-! c₂
    in  ap2 (λ c₁' c₂' → c₁' ◎^ c₂') r₂ r₁
  eval^₁-! (c₁ ⊕ c₂) = 
    let r₁ = eval^₁-! c₁
        r₂ = eval^₁-! c₂
    in  ap2 ++^-⊕ r₁ r₂ ∙ ++^-⊕-! (eval^₁ c₁) (eval^₁ c₂)

  reverse-++ : ∀ {i} {A : Type i} → (l₁ l₂ : List A) → reverse (l₁ ++ l₂) == (reverse l₂) ++ (reverse l₁)
  reverse-++ nil l₂ = ! (++-unit-r _)
  reverse-++ (x :: l₁) l₂ = 
    let r = reverse-++ l₁ l₂
    in  ap (λ l → snoc l x) r ∙ ++-assoc (reverse l₂) (reverse l₁) (x :: nil)

  pi^2list-! : (c : (S n) ⟷₁^ (S m)) → pi^2list (!⟷₁^ c) == transport (λ k → List (Fin k)) (ℕ-S-is-inj _ _ (⟷₁^-eq-size c)) (reverse (pi^2list c))
  pi^2list-! swap₊^ = idp
  pi^2list-! id⟷₁^ = idp
  pi^2list-! (c₁ ◎^ c₂) with (⟷₁^-eq-size c₁) with (⟷₁^-eq-size c₂)
  ... | idp | idp = 
    let r₁ = pi^2list-! c₁
        r₂ = pi^2list-! c₂
    in  ap2 (λ l₁ l₂ → l₁ ++ l₂) r₂ r₁ ∙ ! (reverse-++ (pi^2list c₁) (pi^2list c₂))
  pi^2list-! {O} (⊕^ c) with (⟷₁^-eq-size c)
  ... | idp = idp
  pi^2list-! {S n} (⊕^ c) with (⟷₁^-eq-size c)
  ... | idp = ap (map S⟨_⟩) (pi^2list-! c) ∙ ! (reverse-map S⟨_⟩ (pi^2list c))

  pi^2list-!-nil' : pi^2list (⊕^ eval^₁ (!⟷₁ (quote-eval^₀ (quote^₀ n)))) == nil
  pi^2list-!-nil' {n} =
    ap (λ x → pi^2list (⊕^ x)) (eval^₁-! (quote-eval^₀ (quote^₀ n))) ∙
    pi^2list-! (⊕^ (eval^₁ (quote-eval^₀ (quote^₀ n)))) ∙ 
    transport (λ e → transport (λ k → List (Fin k)) e (reverse (pi^2list (⊕^ eval^₁ (quote-eval^₀ (quote^₀ n))))) == nil) (ℕ-p idp) (ap reverse pi^2list-nil)


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
      _ ⟷₂⟨ TODO ⟩ -- Goal: (((id⟷₁ ⊕ uniti₊l) ◎ assocl₊) ◎ unite₊r ⊕ id⟷₁) ⟷₂ id⟷₁
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
