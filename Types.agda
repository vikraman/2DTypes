{-# OPTIONS --rewriting #-}

module _ where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Universe
open import Rational

infix 60 _⊗_
infix 50 _⊕_

data τ : ℕ → Set where
  𝟘 : τ 0
  𝟙 : τ 1
  _⊕_ : ∀ {m n : ℕ} → τ m → τ n → τ (m + n)
  _⊗_ : ∀ {m n} → τ m → τ n → τ (m * n)

τ-univ : Indexed-universe _ _ _
τ-univ = record { I = ℕ ; U = τ ; El = ⟦_⟧ }
  where ⟦_⟧ : ∀ {n} → τ n → Set
        ⟦ 𝟘 ⟧ = ⊥
        ⟦ 𝟙 ⟧ = ⊤
        ⟦ t₁ ⊕ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
        ⟦ t₁ ⊗ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

data T : ℚ → Set where
  _/_ : ∀ {m n} → τ m → τ n → T (m / n)
  _⊞_ _⊠_ : ∀ {p q} → T p → T q → T (p ++ q)

T-univ : Indexed-universe _ _ _
T-univ = record { I = ℚ ; U = T ; El = ⟦_⟧ }
  where ⟦_⟧ : ∀ {q} → T q → Set
        ⟦ t₁ / t₂ ⟧ = {!!}
        ⟦ t₁ ⊞ t₂ ⟧ = {!!}
        ⟦ t₁ ⊠ t₂ ⟧ = {!!}

open import Function
open import Categories.Category
open import Relation.Binary.PropositionalEquality

τ-cat : ℕ → Category _ _ _
τ-cat n = record { Obj = τ n
                 ; _⇒_ = λ a b → El a → El b
                 ; _≡_ = _≡_
                 ; id = id
                 ; _∘_ = λ g f → g ∘ f
                 ; assoc = refl
                 ; identityˡ = refl
                 ; identityʳ = refl
                 ; equiv = isEquivalence
                 ; ∘-resp-≡ = ∘-resp-≡
                 }
      where open Indexed-universe τ-univ
            ∘-resp-≡ : {A B C : Set} {f h : B → C} {g i : A → B}
                     → f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i
            ∘-resp-≡ refl refl = refl

T-cat : ℚ → Category _ _ _
T-cat q = record { Obj = T q
                 ; _⇒_ = λ a b → El a → El b
                 ; _≡_ = _≡_
                 ; id = id
                 ; _∘_ = λ g f → g ∘ f
                 ; assoc = refl
                 ; identityˡ = refl
                 ; identityʳ = refl
                 ; equiv = isEquivalence
                 ; ∘-resp-≡ = ∘-resp-≡
                 }
      where open Indexed-universe T-univ
            ∘-resp-≡ : {A B C : Set} {f h : B → C} {g i : A → B}
                     → f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i
            ∘-resp-≡ refl refl = refl

module _ where
  open import Data.Nat.Properties.Simple

  *-right-identity : ∀ n → n * 1 ≡ n
  *-right-identity zero = refl
  *-right-identity (suc n) = cong suc (*-right-identity n)

  distribˡ-*-+ : ∀ m n o → m * (n + o) ≡ m * n + m * o
  distribˡ-*-+ m n o = let open ≡-Reasoning in
    begin
      m * (n + o)
    ≡⟨ *-comm m (n + o) ⟩
      (n + o) * m
    ≡⟨ distribʳ-*-+ m n o ⟩
      n * m + o * m
    ≡⟨ cong (λ x → x + o * m) (*-comm n m) ⟩
      m * n + o * m
    ≡⟨ cong (λ x → m * n + x) (*-comm o m) ⟩
      m * n + m * o
    ∎

  {-# BUILTIN REWRITE _≡_ #-}
  {-# REWRITE +-right-identity #-}
  {-# REWRITE +-assoc #-}
  {-# REWRITE *-right-identity #-}
  {-# REWRITE *-assoc #-}
  {-# REWRITE *-right-zero #-}
  {-# REWRITE distribʳ-*-+ #-}
  {-# REWRITE distribˡ-*-+ #-}

infix  30 _⟷_
infixr 50 _◎_

data _⟷_ : ∀ {n} → τ n → τ n → Set where
  unite₊l : ∀ {n} {t : τ n} → 𝟘 ⊕ t ⟷ t
  uniti₊l : ∀ {n} {t : τ n} → t ⟷ 𝟘 ⊕ t
  unite₊r : ∀ {n} {t : τ n} → t ⊕ 𝟘 ⟷ t
  uniti₊r : ∀ {n} {t : τ n} → t ⟷ t ⊕ 𝟘
  swap₊   : ∀ {n} {t₁ t₂ : τ n} → (t₁ ⊕ t₂) ⟷ (t₂ ⊕ t₁)
  assocl₊ : ∀ {n} {t₁ t₂ t₃ : τ n} → t₁ ⊕ (t₂ ⊕ t₃) ⟷ (t₁ ⊕ t₂) ⊕ t₃
  assocr₊ : ∀ {n} {t₁ t₂ t₃ : τ n} → (t₁ ⊕ t₂) ⊕ t₃ ⟷ t₁ ⊕ (t₂ ⊕ t₃)
  unite⋆l : ∀ {n} {t : τ n} → 𝟙 ⊗ t ⟷ t
  uniti⋆l : ∀ {n} {t : τ n} → t ⟷ 𝟙 ⊗ t
  unite⋆r : ∀ {n} {t : τ n} → t ⊗ 𝟙 ⟷ t
  uniti⋆r : ∀ {n} {t : τ n} → t ⟷ t ⊗ 𝟙
  swap⋆   : ∀ {n} {t₁ t₂ : τ n} → t₁ ⊗ t₂ ⟷ t₂ ⊗ t₁
  assocl⋆ : ∀ {n} {t₁ t₂ t₃ : τ n} → t₁ ⊗ (t₂ ⊗ t₃) ⟷ (t₁ ⊗ t₂) ⊗ t₃
  assocr⋆ : ∀ {n} {t₁ t₂ t₃ : τ n} → (t₁ ⊗ t₂) ⊗ t₃ ⟷ t₁ ⊗ (t₂ ⊗ t₃)
  absorbr : ∀ {n} {t : τ n} → 𝟘 ⊗ t ⟷ 𝟘
  absorbl : ∀ {n} {t : τ n} → t ⊗ 𝟘 ⟷ 𝟘
  factorzr : ∀ {n} {t : τ n} → 𝟘 ⟷ t ⊗ 𝟘
  factorzl : ∀ {n} {t : τ n} → 𝟘 ⟷ 𝟘 ⊗ t
  dist : ∀ {n} {t₁ t₂ t₃ : τ n} → (t₁ ⊕ t₂) ⊗ t₃ ⟷ (t₁ ⊗ t₃) ⊕ (t₂ ⊗ t₃)
  factor : ∀ {n} {t₁ t₂ t₃ : τ n} → (t₁ ⊗ t₃) ⊕ (t₂ ⊗ t₃) ⟷ (t₁ ⊕ t₂) ⊗ t₃
  distl : ∀ {n} {t₁ t₂ t₃ : τ n } → t₁ ⊗ (t₂ ⊕ t₃) ⟷ (t₁ ⊗ t₂) ⊕ (t₁ ⊗ t₃)
  factorl : ∀ {n} {t₁ t₂ t₃ : τ n } → (t₁ ⊗ t₂) ⊕ (t₁ ⊗ t₃) ⟷ t₁ ⊗ (t₂ ⊕ t₃)
  id⟷ : ∀ {n} {t : τ n} → t ⟷ t
  _◎_ : ∀ {n} {t₁ t₂ t₃ : τ n} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_ : ∀ {n} {t₁ t₂ t₃ t₄ : τ n} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ⊕ t₂ ⟷ t₃ ⊕ t₄)
  _⊗_ : ∀ {n} {t₁ t₂ t₃ t₄ : τ n} → (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (t₁ ⊗ t₂ ⟷ t₃ ⊗ t₄)

infix 90 !_

!_ : ∀ {n} {t₁ t₂ : τ n} → (t₁ ⟷ t₂) → (t₂ ⟷ t₁)
! unite₊l   = uniti₊l
! uniti₊l   = unite₊l
! unite₊r   = uniti₊r
! uniti₊r   = unite₊r
! swap₊     = swap₊
! assocl₊   = assocr₊
! assocr₊   = assocl₊
! unite⋆l   = uniti⋆l
! uniti⋆l   = unite⋆l
! unite⋆r   = uniti⋆r
! uniti⋆r   = unite⋆r
! swap⋆     = swap⋆
! assocl⋆   = assocr⋆
! assocr⋆   = assocl⋆
! absorbl   = factorzr
! absorbr   = factorzl
! factorzl  = absorbr
! factorzr  = absorbl
! dist      = factor
! factor    = dist
! distl     = factorl
! factorl   = distl
! id⟷       = id⟷
! (c₁ ◎ c₂) = ! c₂ ◎ ! c₁
! (c₁ ⊕ c₂) = ! c₁ ⊕ ! c₂
! (c₁ ⊗ c₂) = ! c₁ ⊗ ! c₂

open import Action

ElT : ∀ q → T q → Σ[ G ∈ Group _ _ ] Σ[ S ∈ Set _ ] Action G S
ElT (p / q) (T₁ / T₂) = {!!} , τ q , {!!}
ElT (._ / ._) (T₁ ⊞ T₂) = {!!}
ElT (._ / ._) (T₁ ⊠ T₂) = {!!}

private
  C₂ : Group _ _
  C₂ = record { Carrier = 𝟙 ⊕ 𝟙 ⟷ 𝟙 ⊕ 𝟙
              ; _≈_ = _≡_
              ; _∙_ = _◎_
              ; ε = id⟷
              ; _⁻¹ = !_
              ; isGroup = record {
                  isMonoid = record {
                    isSemigroup = record {
                      isEquivalence = isEquivalence
                    -- need Pi1 for the holes
                    ; assoc = {!!}
                    ; ∙-cong = {!!}
                    }
                  ; identity = {!!}
                  }
                ; inverse = {!!}
                ; ⁻¹-cong = {!!}
                }
              }

  El1/2 : Σ[ G ∈ Group _ _ ] Σ[ S ∈ Set _ ] Action G S
  El1/2 = C₂ , El (𝟙 ⊕ 𝟙) , record { ρ = λ { (swap₊ , inj₁ tt) → inj₂ tt ; (swap₊ , inj₂ tt) → inj₁ tt
                                           ; (id⟷ , inj₁ tt) → inj₁ tt ; (id⟷ , inj₂ tt) → inj₂ tt
                                           ; (proj₁ ◎ proj₂ , inj₁ tt) → {!!} ; (proj₁ ◎ proj₂ , inj₂ tt) → {!!}
                                           ; (proj₁ ⊕ proj₂ , inj₁ tt) → {!!} ; (proj₁ ⊕ proj₂ , inj₂ tt) → {!!}
                                           }
                                   ; ρ-resp-≈ = {!!}
                                   ; identityA = {!!}
                                   ; compatibility = {!!}
                                   }
        where open Indexed-universe τ-univ
