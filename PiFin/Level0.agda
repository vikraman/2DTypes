{-# OPTIONS --without-K #-}

module PiFin.Level0 where

open import Type using (Type; Type₀; Type₁)
open import Zero using (𝟘)
open import One
open import Coproduct
open import DependentSum using (Σ; _×_; _,_; p₁)
open import NaturalNumbers
open import Functions using (_∘_; id)
open import Equivalences using (_≃_; !e; _●_; qinv-is-equiv; hae-is-qinv; path-to-eqv; ide)

open import Paths using (_==_; refl; _◾_; ap)
open import PathsInSigma using (pair=; dpair=)
open import Univalence using (ua; ua-β; ua-ide)
open import PropositionalTruncation using (∥_∥; ∣_∣; recTrunc; identify)

open import PiFin.EmbeddingsInUniverse using (module UnivalentUniverseOfFiniteTypes)
open UnivalentUniverseOfFiniteTypes

open import PiFin.Syntax

{-

In the model, we have triples: a type T, a size n , and some proof-irrelevant evidence that the size of T is n (specifically, T is equivalent to a flat type of size n)

From U to M:
  We have a structured type A which we map to
  (the denotation of A, the size of A, the truncation of the path from A to its flat form via normalize)

From M to U:
  The only thing we can examine is the size component, so we simply produce fromSize n

U->M->U: we're guaranteed by normalizeC that the flat type and the original are equivalent

M->U->M:
try to make a path between
(X, m, |p|) -> A_m -> (⟦A_m⟧, m, |q|)
Can't do it between X and A_m, but we can do it from |p| to |q|
X = El m = Am \to X = Am, by size-el n


Level 1
Pi to M: From A <-> B, translate to A \eq B, which induces a path on the triple
M to Pi: Have some path between triples (X, n, |p|) and (Y, m, |q|). By dpair=-e\_1, X == Y.
By induction on |p| and |q|, we get a path El m == El n, which from classical math can be converted to a combinator.


-}

-- The model is the subuniverse of finite types
M : Type₁
M = Σ Type₀ is-finite

-- Computes the number of canonical inhabitants of a finite type
size : U → ℕ
size ZERO = 0
size ONE  = 1
size (PLUS  t₁ t₂) = add (size t₁) (size t₂)
size (TIMES t₁ t₂) = mult (size t₁) (size t₂)

canonicalU : U → U
canonicalU = fromSize ∘ size

size+ : (n₁ n₂ : ℕ) → PLUS (fromSize n₁) (fromSize n₂) ⟷ fromSize (add n₁ n₂)
size+ 0         n₂ = unite₊l
size+ (succ n₁) n₂ = assocr₊ ◎ (id⟷ ⊕ size+ n₁ n₂)

size* : (n₁ n₂ : ℕ) → TIMES (fromSize n₁) (fromSize n₂) ⟷ fromSize (mult n₁ n₂)
size* 0         n₂ = absorbr
size* (succ n₁) n₂ = dist ◎ ((unite⋆l ⊕ size* n₁ n₂) ◎ size+ n₂ (mult n₁ n₂))

-- Computes an isomorphism between a finite type and its canonical form
normalizeC : (t : U) → t ⟷ canonicalU t
normalizeC ZERO = id⟷
normalizeC ONE  = uniti₊l ◎ swap₊
normalizeC (PLUS t₀ t₁) =
  (normalizeC t₀ ⊕ normalizeC t₁) ◎ size+ (size t₀) (size t₁)
normalizeC (TIMES t₀ t₁) =
  (normalizeC t₀ ⊗ normalizeC t₁) ◎ size* (size t₀) (size t₁)

#⟦_⟧₀ : U → Type₀
#⟦ ZERO ⟧₀        = 𝟘
#⟦ ONE  ⟧₀        = 𝟙
#⟦ PLUS  t₁ t₂ ⟧₀ = #⟦ t₁ ⟧₀ + #⟦ t₂ ⟧₀
#⟦ TIMES t₁ t₂ ⟧₀ = #⟦ t₁ ⟧₀ × #⟦ t₂ ⟧₀

size-el : (n : ℕ) → #⟦ fromSize n ⟧₀ == El n
size-el = indℕ _ (refl 𝟘) (λ _ → ap (_+_ 𝟙))

#⟦_⟧₁ : {X Y : U} → X ⟷ Y → #⟦ X ⟧₀ ≃ #⟦ Y ⟧₀
#⟦ id⟷ ⟧₁ = ide _
#⟦ unite₊l ⟧₁ = (λ { (i₁ ()); (i₂ x) → x }) ,
  qinv-is-equiv (i₂ , (λ { (i₁ ()); x@(i₂ _) → refl x }) , refl)
#⟦ swap₊ ⟧₁ = (λ { (i₁ x) → i₂ x; (i₂ x) → i₁ x }) ,
  qinv-is-equiv ((λ { (i₁ x) → i₂ x; (i₂ x) → i₁ x }) ,
    (λ { x@(i₁ _) → refl x; x@(i₂ _) → refl x }) ,
    (λ { x@(i₁ _) → refl x; x@(i₂ _) → refl x }))
#⟦ assocl₊ ⟧₁ = (λ { (i₁ x) → i₁ (i₁ x); (i₂ (i₁ x)) → i₁ (i₂ x); (i₂ (i₂ x)) → i₂ x }) ,
  qinv-is-equiv ((λ { (i₁ (i₁ x)) → i₁ x; (i₁ (i₂ x)) → i₂ (i₁ x); (i₂ x) → i₂ (i₂ x) }) ,
    (λ { x@(i₁ _) → refl x; x@(i₂ (i₁ _)) → refl x; x@(i₂ (i₂ _)) → refl x }) ,
    (λ { x@(i₁ (i₁ _)) → refl x; x@(i₁ (i₂ _)) → refl x; x@(i₂ _) → refl x }))
#⟦ unite⋆l ⟧₁ = (λ { (_ , x) → x }) ,
  qinv-is-equiv ((λ x → (0₁ , x)) , (λ { x@(0₁ , _) → refl x }) , refl)
#⟦ swap⋆ ⟧₁ = (λ { (x , y) → (y , x) }) , qinv-is-equiv ((λ { (x , y) → (y , x) }) , refl , refl)
#⟦ assocl⋆ ⟧₁ = (λ { (x , y , z) → ((x , y) , z) }) ,
  qinv-is-equiv ((λ { ((x , y) , z) → x , y , z }) , refl , refl)
#⟦ absorbr ⟧₁ = (λ { (() , _) }) , qinv-is-equiv ((λ ()) , (λ { (() , _) }) , (λ ()))
#⟦ dist ⟧₁ = (λ { (i₁ x , y) → i₁ (x , y); (i₂ x , y) → i₂ (x , y) }) ,
  qinv-is-equiv ((λ { (i₁ (x , y)) → i₁ x , y; (i₂ (x , y)) → i₂ x , y }) ,
    (λ { x@(i₁ _ , _) → refl x; x@(i₂ _ , _) → refl x }) ,
    (λ { x@(i₁ _) → refl x; x@(i₂ _) → refl x }))
{- #⟦ distl ⟧₁ = (λ { (x , i₁ y) → i₁ (x , y); (x , i₂ y) → i₂ (x , y) }) ,
  qinv-is-equiv ((λ { (i₁ (x , y)) → x , i₁ y; (i₂ (x , y)) → x , i₂ y }) ,
    (λ { x@(_ , i₁ _) → refl x; x@(_ , i₂ _) → refl x }) ,
    (λ { x@(i₁ _) → refl x; x@(i₂ _) → refl x }))-}
#⟦ _⟷_.! f ⟧₁ = !e #⟦ f ⟧₁
#⟦ f ◎ g ⟧₁ = #⟦ g ⟧₁ ● #⟦ f ⟧₁
#⟦ f ⊕ g ⟧₁ =
  let (f , e) = #⟦ f ⟧₁ in
  let (f⁻¹ , εf , ηf) = hae-is-qinv e in
  let (g , e) = #⟦ g ⟧₁ in
  let (g⁻¹ , εg , ηg) = hae-is-qinv e in
  (λ { (i₁ x) → i₁ (f x); (i₂ x) → i₂ (g x) }) ,
    qinv-is-equiv ((λ { (i₁ y) → i₁ (f⁻¹ y); (i₂ y) → i₂ (g⁻¹ y) }) ,
      (λ { (i₁ x) → ap i₁ (εf x); (i₂ x) → ap i₂ (εg x) }) ,
      (λ { (i₁ y) → ap i₁ (ηf y); (i₂ y) → ap i₂ (ηg y) }))
#⟦ f ⊗ g ⟧₁ =
  let (f , e) = #⟦ f ⟧₁ in
  let (f⁻¹ , εf , ηf) = hae-is-qinv e in
  let (g , e) = #⟦ g ⟧₁ in
  let (g⁻¹ , εg , ηg) = hae-is-qinv e in
  (λ { (a , b) → (f a , g b) }) ,
    qinv-is-equiv ((λ { (c , d) → (f⁻¹ c , g⁻¹ d) }) ,
      (λ { (a , b) → pair= (εf a , εg b) }) ,
      (λ { (c , d) → pair= (ηf c , ηg d) }))

⟦_⟧₀ : U → M
⟦ T ⟧₀ = #⟦ T ⟧₀ , size T , ∣ ua #⟦ normalizeC T ⟧₁ ◾ size-el _ ∣

-- Can't induct over the type in the first component, so return
-- the next best thing
⟦_⟧₀⁻¹ : M → U
⟦ _ , n , _ ⟧₀⁻¹ = fromSize n

-- This is risky: the only reason we are able to explicitly give
-- normalizeC as a path is because we know that the image of the translation
-- in the model has truncated paths of the form ∣ ua #⟦ normalizeC ... ⟧₁ ∣
⟦⟦_⟧₀⟧₀⁻¹ : (T : U) → ⟦ ⟦ T ⟧₀ ⟧₀⁻¹ ⟷ T
⟦⟦ T ⟧₀⟧₀⁻¹ = ! (normalizeC T)

⟦⟦_⟧₀⁻¹⟧₀ : (X : M) → ∥ ⟦ ⟦ X ⟧₀⁻¹ ⟧₀ == X ∥
⟦⟦ X@(T , n , p) ⟧₀⁻¹⟧₀ = recTrunc _ (∣_∣ ∘ lem) identify p where
  lem : T == El n → ⟦ ⟦ X ⟧₀⁻¹ ⟧₀ == X
  lem (refl _) = p₁ (finite-types-is-univ _ _) (path-to-eqv (size-el n))
    {- Alternative proof:
         p₁ (finite-types-is-univ ⟦ ⟦ X ⟧₀⁻¹ ⟧₀ X) (path-to-eqv (size-el n ◾ Paths.! p')) -}

-- TODO: Better names
sound₀ : (T : U) → Σ M (λ X → ⟦ X ⟧₀⁻¹ ⟷ T)
sound₀ T = ⟦ T ⟧₀ , ⟦⟦ T ⟧₀⟧₀⁻¹

-- We know there exists a path, but we cannot distinguish it concretely, since
-- the path between a type in the semiring and its normal form is truncated.
cmpl₀ : (X : M) → Σ U (λ T → ∥ ⟦ T ⟧₀ == X ∥)
cmpl₀ X = ⟦ X ⟧₀⁻¹ , ⟦⟦ X ⟧₀⁻¹⟧₀
