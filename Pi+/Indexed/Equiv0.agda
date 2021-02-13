{-# OPTIONS --without-K --exact-split --allow-unsolved-metas --rewriting #-}

module Pi+.Indexed.Equiv0 where

open import Pi+.Indexed.Syntax as Pi
open import Pi+.Indexed.SyntaxNorm as Pi^
open import Pi+.UFin
-- open import Pi+.Level0
open import Pi+.Extra

open import lib.Basics
open import lib.types.Fin
open import lib.types.List
open import lib.types.Truncation
open import lib.NType2
open import lib.types.SetQuotient
open import lib.types.Coproduct
open import lib.types.Nat as N

-- ∣⟪_⟫∣ : (n : ℕ) → ∣ ⟪ n ⟫ ∣ == n
-- ∣⟪ O ⟫∣ = idp
-- ∣⟪ S n ⟫∣ = ap S ∣⟪ n ⟫∣

private
  variable
    n m o p : ℕ

_++^_ : U^ m → U^ n → U^ (m N.+ n)
O ++^ t₂ = t₂
(I+ t₁) ++^ t₂ = I+ (t₁ ++^ t₂)

++^-unit : {t : U^ m} → t ⟷₁^ (t ++^ O)
++^-unit {t = O} = id⟷₁^
++^-unit {t = I+ t} = ⊕^ ++^-unit {t = t}

++^-assoc : (t₁ : U^ m) (t₂ : U^ n) (t₃ : U^ o) → (t₁ ++^ (t₂ ++^ t₃)) ⟷₁^ ((t₁ ++^ t₂) ++^ t₃)
++^-assoc O t₂ t₃ = id⟷₁^
++^-assoc (I+ t₁) t₂ t₃ = ⊕^ ++^-assoc t₁ t₂ t₃

++^-cons : (t : U^ n) → I+ t ⟷₁^ (t ++^ (I+ O))
++^-cons O = id⟷₁^
++^-cons (I+ t) = swap₊^ ◎^ (⊕^ (++^-cons t))

++^-⊕ : {t₁ : U^ m} {t₂ : U^ n} {t₃ : U^ o} {t₄ : U^ p} → (t₁ ⟷₁^ t₂) → (t₃ ⟷₁^ t₄) → (t₁ ++^ t₃) ⟷₁^ (t₂ ++^ t₄)
++^-⊕ (swap₊^ {t = t}) c₂ = big-swap₊^ (++^-⊕ (id⟷₁^ {t = t}) c₂)
++^-⊕ {t₁ = O} id⟷₁^ c₂ = c₂
++^-⊕ {t₁ = I+ t₁} id⟷₁^ c₂ = ⊕^ (++^-⊕ id⟷₁^ c₂)
++^-⊕ (c₁ ◎^ c₃) c₂ = (++^-⊕ c₁ c₂) ◎^ ++^-⊕ c₃ id⟷₁^
++^-⊕ (⊕^ c₁) c₂ = ⊕^ (++^-⊕ c₁ c₂)

++^-swap : (t₁ : U^ m) (t₂ : U^ n) → (t₁ ++^ t₂) ⟷₁^ (t₂ ++^ t₁)
++^-swap O t₂ = ++^-unit {t = t₂}
++^-swap (I+ t₁) t₂ = (⊕^ ++^-swap t₁ t₂) ◎^ ++^-cons (t₂ ++^ t₁) ◎^ !⟷₁^ (++^-assoc t₂ t₁ (I+ O)) ◎^ ++^-⊕ id⟷₁^ (!⟷₁^ (++^-cons t₁))

quote^₀ : U^ n → U n
quote^₀ O = O
quote^₀ (I+ X) = I U.+ quote^₀ X

quote^₁ : {t₁ : U^ n} {t₂ : U^ m} → (t₁ ⟷₁^ t₂) → (quote^₀ t₁ ⟷₁ quote^₀ t₂)
quote^₁ swap₊^ = assocl₊ ◎ (swap₊ ⊕ id⟷₁) ◎ assocr₊
quote^₁ id⟷₁^ = id⟷₁
quote^₁ (t ◎^ t₁) = quote^₁ t ◎ quote^₁ t₁
quote^₁ (⊕^ t) = id⟷₁ ⊕ quote^₁ t

quote^₀++ : (t₁ : U^ n) (t₂ : U^ m) → quote^₀ (t₁ ++^ t₂) ⟷₁ quote^₀ t₁ U.+ quote^₀ t₂
quote^₀++ O t₂ = uniti₊l
quote^₀++ (I+ t₁) t₂ = (id⟷₁ ⊕ quote^₀++ t₁ t₂) ◎ assocl₊

quoteNorm₀ : {n : ℕ} -> UFin[ n ] → U^ n
quoteNorm₀ {O} _ = O
quoteNorm₀ {S n} _ = I+ quoteNorm₀ (pFin n)

quote₀ : UFin[ n ] → U n
quote₀ = quote^₀ ∘ quoteNorm₀

eval^₀ : U n → U^ n
eval^₀ O = O
eval^₀ I = I+ O
eval^₀ (t₁ U.+ t₂) = eval^₀ t₁ ++^ eval^₀ t₂

evalNorm₀ : U^ n → UFin[ n ]
evalNorm₀ _ = pFin _

eval₀ : U n → UFin[ n ]
eval₀ = evalNorm₀ ∘ eval^₀

quote-eval^₀ : (t : U n) → quote^₀ (eval^₀ t) ⟷₁ t
quote-eval^₀ O = id⟷₁
quote-eval^₀ I = swap₊ ◎ unite₊l
quote-eval^₀ (t₁ U.+ t₂) = quote^₀++ (eval^₀ t₁) (eval^₀ t₂) ◎ (quote-eval^₀ t₁ ⊕ quote-eval^₀ t₂)

quote-evalNorm₀ : (t : U^ n) → quoteNorm₀ (evalNorm₀ t) ⟷₁^ t
quote-evalNorm₀ O = id⟷₁^
quote-evalNorm₀ (I+ t) = ⊕^ quote-evalNorm₀ t 

quote-eval₀ : (t : U n) → quote₀ (eval₀ t) ⟷₁ t
quote-eval₀ t = quote^₁ (quote-evalNorm₀ (eval^₀ t)) ◎ quote-eval^₀ t

eval-quote^==₀ : (t : U^ n) → eval^₀ (quote^₀ t) == t
eval-quote^==₀ O = idp
eval-quote^==₀ (I+ t) = ap I+_ (eval-quote^==₀ t)

eval-quote^₀ : (t : U^ n) → eval^₀ (quote^₀ t) ⟷₁^ t
eval-quote^₀ O = id⟷₁^
eval-quote^₀ (I+ t) = ⊕^ eval-quote^₀ t

eval-quoteNorm₀ : {n : ℕ} (X : UFin[ n ]) → Trunc -1 (evalNorm₀ (quoteNorm₀ X) == X)
eval-quoteNorm₀ (X , ϕ) = Trunc-fmap (λ p → pair= p prop-has-all-paths-↓) ϕ

eval-quote₀ : {n : ℕ} (X : UFin[ n ]) → Trunc -1 (eval₀ (quote₀ X) == X)
eval-quote₀ = eval-quoteNorm₀