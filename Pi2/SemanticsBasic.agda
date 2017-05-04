{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Pi2.SemanticsBasic where

open import UnivalentTypeTheory
open import PropositionalTruncation

open import UniFibExamples using (Ω)
open import TwoUniverse using (all-1-paths ; +fn)
                        renaming (U[𝟚] to M
                                  ; U[𝟚]-is-path-conn to M-is-path-conn
                                  ; `not to not-path
                                  ; `ρ to ρ
                                  ; U[𝟚]-is-1type to M-is-1type)

open import Pi2.Syntax hiding (_⟷₂_ ; _◾₂_ ; !₂_)

module AdjustId where
  -- The `id and `ρ in TwoUniverse are not exactly the ones we want

  adjust-id : ==' (Ω M (𝟚 , ∣ refl 𝟚 ∣))
                  (dpair= (refl 𝟚 , identify _ _))
                  (refl (𝟚 , ∣ refl 𝟚 ∣))
  adjust-id = ap dpair= (dpair= (refl (refl 𝟚) , prop-is-set identify _ _ _ _)) ◾ dpair=-η _

  ρ' : not-path ◾ not-path == refl (𝟚 , ∣ refl 𝟚 ∣)
  ρ' = ρ ◾ adjust-id

  all-1-paths' : (p : (𝟚 , ∣ refl 𝟚 ∣) == (𝟚 , ∣ refl 𝟚 ∣))
                 → (p == refl (𝟚 , ∣ refl 𝟚 ∣)) + (p == not-path)
  all-1-paths' = +fn (λ α → α ◾ adjust-id) id ∘ all-1-paths

open AdjustId using (ρ' ; all-1-paths')


module _ where

  infixr 3 _⟷₂_
  infix 5 !₂
  infixr 4 _◾₂_

  data _⟷₂_ : {A B : U} (p q : A ⟷₁ B) → Set where
    _◾₂_ : {A B : U} {p q r : A ⟷₁ B} → (p ⟷₂ q) → (q ⟷₂ r) → (p ⟷₂ r)
    `assoc₂ : {A B C D : U} → (p : A ⟷₁ B) → (q : B ⟷₁ C) → (r : C ⟷₁ D)
              → (p ◾₁ q) ◾₁ r ⟷₂ p ◾₁ (q ◾₁ r)
    `id₂ : {A B : U} (p : A ⟷₁ B) → p ⟷₂ p
    `idl : {A B : U} (p : A ⟷₁ B) → `id ◾₁ p ⟷₂ p
    `idr : {A B : U} (p : A ⟷₁ B) → p ◾₁ `id ⟷₂ p

    !₂ : {A B : U} {p q : A ⟷₁ B} → (p ⟷₂ q) → q ⟷₂ p
    `!r : {A B : U} (p : A ⟷₁ B) → p ◾₁ !₁ p ⟷₂ `id
    `!l : {A B : U} (p : B ⟷₁ A) → !₁ p ◾₁ p ⟷₂ `id

    _□₂_ : {A B C : U} {p q : A ⟷₁ B} {r s : B ⟷₁ C}
           → (p ⟷₂ q) → (r ⟷₂ s) → (p ◾₁ r) ⟷₂ (q ◾₁ s)

    `ρ : `not ◾₁ `not ⟷₂ `id


module _ where
  -- We neglect term judgments at level 0

  ⟦_⟧ᵀ₀ : U → M
  ⟦ `𝟚 ⟧ᵀ₀ = (𝟚 , ∣ refl 𝟚 ∣)


module _ where
  -- We collapse type and term judgments at levels > 0

  ⟦_⟧ᵗ₁ : {X Y : U} → (p : X ⟷₁ Y) → ⟦ X ⟧ᵀ₀ == ⟦ Y ⟧ᵀ₀
  ⟦ `id ⟧ᵗ₁ = refl _
  ⟦ `not ⟧ᵗ₁ = not-path
  ⟦ !₁ p ⟧ᵗ₁ = ! ⟦ p ⟧ᵗ₁
  ⟦ p ◾₁ q ⟧ᵗ₁ = ⟦ p ⟧ᵗ₁ ◾ ⟦ q ⟧ᵗ₁


module _ where

  ⟦_⟧ᵗ₂ : {X Y : U} → {p q : X ⟷₁ Y} → (p ⟷₂ q) → ⟦ p ⟧ᵗ₁ == ⟦ q ⟧ᵗ₁
  ⟦ α ◾₂ β ⟧ᵗ₂ = ⟦ α ⟧ᵗ₂ ◾ ⟦ β ⟧ᵗ₂
  ⟦ `assoc₂ p q r ⟧ᵗ₂ = ◾assoc ⟦ p ⟧ᵗ₁ ⟦ q ⟧ᵗ₁ ⟦ r ⟧ᵗ₁
  ⟦ `id₂ p ⟧ᵗ₂ = refl ⟦ p ⟧ᵗ₁
  ⟦ `idl p ⟧ᵗ₂ = ◾unitl ⟦ p ⟧ᵗ₁
  ⟦ `idr p ⟧ᵗ₂ = ◾unitr ⟦ p ⟧ᵗ₁
  ⟦ !₂ α ⟧ᵗ₂ = ! ⟦ α ⟧ᵗ₂
  ⟦ `!r p ⟧ᵗ₂ = ◾invr ⟦ p ⟧ᵗ₁
  ⟦ `!l p ⟧ᵗ₂ = ◾invl ⟦ p ⟧ᵗ₁
  ⟦ α □₂ β ⟧ᵗ₂ = ⟦ α ⟧ᵗ₂ [2,0,2] ⟦ β ⟧ᵗ₂
  ⟦ `ρ ⟧ᵗ₂ = ρ'


module CompletenessZero where
  -- Type judgments at level 0

  cmpl0 : (x : M) → Σ U (λ `x → ∥ ⟦ `x ⟧ᵀ₀ == x ∥)
  cmpl0 x = `𝟚 , p₂ M-is-path-conn _ _

module CompletenessOne where
  -- Term judgments at level 1

  cmpl1-Ω : (p : Ω M (𝟚 , ∣ refl 𝟚 ∣))
            → Σ (`𝟚 ⟷₁ `𝟚) (λ `p → ⟦ `p ⟧ᵗ₁ == p)
  cmpl1-Ω p with (all-1-paths' p)
  ...       | i₁ α = `id , ! α
  ...       | i₂ α = `not , ! α

open CompletenessOne

module CompletenessTwoLemma where

  cmpl2-lem : (p : `𝟚 ⟷₁ `𝟚) → (p ⟷₂ `id) + (p ⟷₂ `not)
  cmpl2-lem' : {X : U} → (p : `𝟚 ⟷₁ X) → (q : X ⟷₁ `𝟚)
                → (p ◾₁ q ⟷₂ `id) + (p ◾₁ q ⟷₂ `not)

  cmpl2-lem' {`𝟚} p q with (cmpl2-lem p) | (cmpl2-lem q)
  ...                  | (i₁ α) | (i₁ β) = i₁ ((α □₂ β) ◾₂ `idr `id)
  ...                  | (i₁ α) | (i₂ β) = i₂ ((α □₂ β) ◾₂ `idl `not)
  ...                  | (i₂ α) | (i₁ β) = i₂ ((α □₂ β) ◾₂ `idr `not)
  ...                  | (i₂ α) | (i₂ β) = i₁ ((α □₂ β) ◾₂ `ρ)

  cmpl2-lem `id = i₁ (`id₂ _)
  cmpl2-lem `not = i₂ (`id₂ _)
  cmpl2-lem (!₁ p) with (cmpl2-lem p)
  ...               | (i₁ α) = i₁ (!₂ (`idr (!₁ p))
                                      ◾₂ !₂ (`id₂ (!₁ p) □₂ α)
                                      ◾₂ `!l p)
  ...               | (i₂ α) = i₂ (!₂ (!₂ ((`!l p □₂ `id₂ `not) ◾₂ `idl `not)
                                      ◾₂ (`id₂ (!₁ p) □₂ α) □₂ `id₂ `not
                                      ◾₂ `assoc₂ (!₁ p) `not `not
                                         ◾₂ (`id₂ (!₁ p) □₂ `ρ)
                                         ◾₂ `idr (!₁ p)))
  cmpl2-lem (p ◾₁ q) = cmpl2-lem' p q

open CompletenessTwoLemma

module CompletenessTwo where
  -- Term judgments at level 2

  cmpl2-Ω : {p q : Ω M (𝟚 , ∣ refl 𝟚 ∣)} → (α : p == q)
            → Σ (`𝟚 ⟷₁ `𝟚) (λ `p →
               Σ (`𝟚 ⟷₁ `𝟚) (λ `q →
               Σ (p == ⟦ `p ⟧ᵗ₁) (λ r →
               Σ (⟦ `q ⟧ᵗ₁ == q) (λ s →
               Σ (`p ⟷₂ `q) (λ `α →
                 r ◾ ⟦ `α ⟧ᵗ₂ ◾ s == α)))))
  cmpl2-Ω (refl p) with cmpl2-lem (p₁ (cmpl1-Ω p))
  cmpl2-Ω (refl p) | i₁ `α = p₁ (cmpl1-Ω p) , p₁ (cmpl1-Ω p) ,
                             ! (p₂ (cmpl1-Ω p)) , p₂ (cmpl1-Ω p) ,
                             (`α ◾₂ !₂ `α) , M-is-1type _ _ _ _ _ _
  cmpl2-Ω (refl p) | i₂ `α = p₁ (cmpl1-Ω p) , p₁ (cmpl1-Ω p) ,
                             ! (p₂ (cmpl1-Ω p)) , p₂ (cmpl1-Ω p) ,
                             (`α ◾₂ !₂ `α) , M-is-1type _ _ _ _ _ _
