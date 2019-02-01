{-# OPTIONS --without-K --rewriting #-}

module PiS1.Semantics where

open import HoTT
open import homotopy.LoopSpaceCircle

is-type-[_] : Type₀ → Type₀ → Type₁
is-type-[ T ] X = Trunc -1 (T == X)

M : Type₁
M = Σ Type₀ (is-type-[ S¹ ])

M₀ : M
M₀ = S¹ , [ idp ]

-- BAut : ∀ {ℓ} → Type ℓ → Type (lsucc ℓ)
-- BAut {ℓ} T = Σ (Type ℓ) λ X → Trunc -1 (T == X)

⊙BAut : ∀ {ℓ} → Type ℓ → Ptd (lsucc ℓ)
⊙BAut T = ⊙[ BAut T , (T , [ idp ]) ]

-- BAut-trunc-path : ∀ {ℓ} (T X : Type ℓ) (φ : Trunc -1 (T == X))
--                 → Trunc -1 ((T , [ idp ]) == (X , φ) :> BAut T)
-- BAut-trunc-path {ℓ} T X = Trunc-elim λ p → [ pair= p prop-has-all-paths-↓ ]

BAut-0-conn : ∀ {ℓ} (T : Type ℓ) → is-connected 0 (BAut T)
BAut-0-conn T = has-level-in ( [ pt (⊙BAut T) ]
                             , Trunc-elim λ { (X , φ) → <– (=ₜ-equiv [ T , [ idp ] ] [ X , φ ])
                                                           (BAut-trunc-path T X φ) } )

N : Type₁
N = BAut S¹

M≃N : M ≃ N
M≃N = ide M

M=N : M == N
M=N = idp

BAut-SubtypeProp : ∀ {ℓ} → (T : Type ℓ) → SubtypeProp (Type ℓ) (lsucc ℓ)
BAut-SubtypeProp T = (λ X → Trunc -1 (T == X)) , (λ _ → Trunc-level)

BAut-level : ∀ {ℓ} {n : ℕ₋₂} {T : Type ℓ} {{φ : has-level n T}} → (X : BAut T) → has-level n (fst X)
BAut-level {n = n} {{φ}} (X , ψ) = Trunc-elim (λ p → transport (has-level n) p φ) ψ

BAut= : ∀ {ℓ} {T : Type ℓ} (X Y : BAut T) → Type (lsucc ℓ)
BAut= {T = T} = Subtype= (BAut-SubtypeProp T)

BAut=-econv : ∀ {ℓ} {T : Type ℓ} (X Y : BAut T) → (BAut= X Y) ≃ (X == Y)
BAut=-econv {T = T} = Subtype=-econv (BAut-SubtypeProp T)

_-BAut-level : ∀ {ℓ} (n : ℕ₋₂) {T : Type ℓ} {{φ : has-level n T}} → has-level (S n) (BAut T)
_-BAut-level n {{φ}} =
  has-level-in λ { X Y → equiv-preserves-level (BAut=-econv X Y)
                         {{universe-=-level (BAut-level X) (BAut-level Y)}} }

instance
  BAut-prop-is-set : ∀ {ℓ} {T : Type ℓ} → {{φ : is-prop T}} → is-set (BAut T)
  BAut-prop-is-set = S ⟨-2⟩ -BAut-level

  BAut-set-is-gpd : ∀ {ℓ} {T : Type ℓ} → {{φ : is-set T}} → is-gpd (BAut T)
  BAut-set-is-gpd = S (S ⟨-2⟩) -BAut-level

  BAut-gpd-is-2-gpd : ∀ {ℓ} {T : Type ℓ} → {{φ : is-gpd T}} → has-level 2 (BAut T)
  BAut-gpd-is-2-gpd = S (S (S ⟨-2⟩)) -BAut-level

N-is-2-gpd : has-level 2 N
N-is-2-gpd = ⟨⟩

M-is-gpd : has-level 2 M
M-is-gpd = ⟨⟩

is-univ-fib : ∀ {i j} {A : Type i} (B : A → Type j) → Type (lmax i j)
is-univ-fib B = ∀ {x y} → is-equiv (transport-equiv B {x} {y})

tpt-eqv-fst : ∀ {i j} {P : Type i → Type j} {X Y : Type i} → (p : X == Y)
            → {ux : P X} {uy : P Y} → (up : ux == uy [ P ↓ p ])
            → transport-equiv fst (pair= p up) == coe-equiv p
tpt-eqv-fst idp idp = idp

Subtype-is-univ : ∀ {i j} (P : SubtypeProp (Type i) j) → is-univ-fib (fst {A = Type i} {B = fst P})
Subtype-is-univ P {X , φ₁} {Y , φ₂} = is-eq f g f-g g-f
  where f : X , φ₁ == Y , φ₂ → X ≃ Y
        f = transport-equiv fst
        g : X ≃ Y → X , φ₁ == Y , φ₂
        g e = Subtype=-out P (ua e)
        f-g : (b : X ≃ Y) → f (g b) == b
        f-g b = tpt-eqv-fst (ua b) prop-has-all-paths-↓ ∙ coe-equiv-β b
        g-f : (a : X , φ₁ == Y , φ₂) → g (f a) == a
        g-f idp = pair== (ua-η idp) prop-has-all-paths-↓ ∙ ! (pair=-η idp)
          where instance _ = snd P X

is-type-[_]-SubtypeProp : ∀ T → SubtypeProp Type₀ (lsucc lzero)
is-type-[ T ]-SubtypeProp = is-type-[ T ] , ⟨⟩

is-type-[_]-is-univ : ∀ T → is-univ-fib (fst {A = Type₀} {is-type-[ T ]})
is-type-[ T ]-is-univ = Subtype-is-univ is-type-[ T ]-SubtypeProp

loop≠idp : loop ≠ idp
loop≠idp r = {!!}
  where K : ∀ {i} {A : Type i} {x : A} (p : x == x) → p == idp
        K {x = x} p =
          let f = S¹Rec.f x p
              loop-β = S¹Rec.loop-β x p in
          p         =⟨ ! loop-β ⟩
          ap f loop =⟨ ap (λ q → ap f q) r ⟩
          idp =∎

rotate : ℤ → S¹ → S¹
rotate z = S¹-rec base (loop^ z)

rotate-right : S¹ → S¹
rotate-right = rotate 1

rotate-right-is-id : (x : S¹) → rotate-right x == x
rotate-right-is-id x = S¹-rec base (loop^ 1) x =⟨ ap (λ p → S¹-rec base p x) idp ⟩
                       S¹-rec base loop x =⟨ ap (λ p → S¹-rec base p x) (! (ap-idf loop)) ⟩
                       S¹-rec base (ap (idf S¹) loop) x =⟨ S¹-rec-η (idf S¹) x ⟩
                       x =∎

rotate-right-is-equiv : is-equiv rotate-right
rotate-right-is-equiv = transport is-equiv (λ= (λ x → ! (rotate-right-is-id x))) (idf-is-equiv S¹)

_ℤ*_ : ℤ → ℤ → ℤ
_ℤ*_ = {!!}

rotate-∙ : ∀ {m n} → (x : S¹) → (rotate m ∘ rotate n) x == rotate (m ℤ* n) x
rotate-∙ {m} {n} x = S¹-rec base (loop^ m) (S¹-rec base (loop^ n) x) =⟨ {!!} ⟩
                     S¹-rec base (loop^ (m ℤ* n)) x =∎

rotate-left : S¹ → S¹
rotate-left = rotate (negsucc 0)

rotate-left-left-is-id : (x : S¹) → rotate-left (rotate-left x) == x
rotate-left-left-is-id x = S¹-rec base (loop^ (negsucc 0)) (S¹-rec base (loop^ (negsucc 0)) x) =⟨ {!!} ⟩
                           S¹-rec base loop x =⟨ ap (λ p → S¹-rec base p x) (! (ap-idf loop)) ⟩
                           S¹-rec base (ap (idf S¹) loop) x =⟨ S¹-rec-η (idf S¹) x ⟩
                           x =∎

rotate-left-is-equiv : is-equiv rotate-left
rotate-left-is-equiv = is-eq rotate-left rotate-left rotate-left-left-is-id rotate-left-left-is-id

Aut : ∀ {i} → Type i → Type i
Aut T = T ≃ T

a₀ : Aut S¹
a₀ = rotate-right , rotate-right-is-equiv

a₀-is-ide : a₀ == ide S¹
a₀-is-ide = pair= (λ= rotate-right-is-id) prop-has-all-paths-↓

a₁ : Aut S¹
a₁ = rotate-left , rotate-left-is-equiv

p₀ : (x : S¹) → x == x
p₀ x = idp

p₁ : (x : S¹) → x == x
p₁ = S¹-elim loop (↓-idf=idf-in' (∙=∙' loop loop))

p₁≠p₀ : p₁ ≠ p₀
p₁≠p₀ p = loop≠idp (app= p base)

b₀ : a₀ == a₀
b₀ = pair= (λ= (λ x → ap rotate-right (p₀ x))) prop-has-all-paths-↓

b₁ : a₀ == a₀
b₁ = pair= (λ= (λ x → ap rotate-right (p₁ x))) prop-has-all-paths-↓

c₀ : a₁ == a₁
c₀ = pair= (λ= (λ x → ap rotate-left (p₀ x))) prop-has-all-paths-↓

c₁ : a₁ == a₁
c₁ = pair= (λ= (λ x → ap rotate-left (p₁ x))) prop-has-all-paths-↓

t₀ : Trunc 0 (Aut S¹) == Bool
t₀ = {!!}

t₁ : Ω ⊙[ Aut S¹ , a₀ ] == ℕ
t₁ = {!!}

open import PiS1.Syntax

⟦_⟧₀ : U → Set₁
⟦ S ⟧₀ = M

⟦_⟧₁ : {A B : U} → (p : A ⟷₁ B) → ⟦ A ⟧₀ == ⟦ B ⟧₀
⟦ id ⟧₁ = {!!}
⟦ flip ⟧₁ = {!!}

⟦_⟧₂ : {A B : U} {p q : A ⟷₁ B} → (u : p ⟷₂ q) → ⟦ p ⟧₁ == ⟦ q ⟧₁
⟦ z ⟧₂ = {!!}
⟦ s q ⟧₂ = {!!}
