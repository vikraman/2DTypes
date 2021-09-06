{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

module Pi.UFin.Univ where

open import HoTT hiding (transport-equiv)

private
  variable
    i j k l : ULevel

transport-equiv : {A : Type i} (P : A → Type j) {x y : A} (p : x == y) → (P x ≃ P y)
transport-equiv P p = coe-equiv (ap P p)

transport-equiv-idf :
  {X Y : Type i} (p : X == Y) →
  transport-equiv (idf (Type i)) p == coe-equiv p
transport-equiv-idf p = pair= (ap coe (ap-idf p)) prop-has-all-paths-↓

transport-equiv-fst :
  {P : Type i → Type j} {X Y : Type i} (p : X == Y) →
  {ux : P X} {uy : P Y} (up : ux == uy [ P ↓ p ]) →
  transport-equiv fst (pair= p up) == coe-equiv p
transport-equiv-fst p up = pair= (ap coe (fst=-β p up)) prop-has-all-paths-↓

is-univ-fib : {A : Type i} (P : A → Type j) → Type (lmax i j)
is-univ-fib P = ∀ {x y} → is-equiv (transport-equiv P {x} {y})

module _ {A : Type i} (P : A → Type j) where

  tot : Type (lmax i j)
  tot = Σ A P

  =tot : tot → tot → Type (lmax i j)
  =tot = =Σ

  fib : tot → A
  fib = fst

  fib-lift : {x y : A} {u : P x} (p : x == y) → =tot (x , u) (y , transport P p u)
  fib-lift p = p , from-transp P p idp

record UU (i j : ULevel) : Type (lmax (lsucc i) (lsucc j)) where
  constructor UU[_,_]
  field
    U : Type i
    El : U → Type j

UU-Σ : UU i j ≃ tot (λ U → U → Type j)
UU-Σ = equiv f g (λ _ → idp) (λ _ → idp)
  where f : _
        f UU[ U , El ] = U , El
        g : _
        g (U , El) = UU[ U , El ]

is-univalent : (U : UU i j) → Type _
is-univalent U = is-univ-fib (UU.El U)

module _ (Ũ : UU i j) (ϕ : is-univalent Ũ) where
  open UU Ũ

  UU-ua : {X Y : U} → El X ≃ El Y → X == Y
  UU-ua = is-equiv.g ϕ

  UU-ua-β : {X Y : U} → (e : El X ≃ El Y) → coe-equiv (ap El (UU-ua e)) == e
  UU-ua-β = is-equiv.f-g ϕ

TypeUU : (i : ULevel) → UU (lsucc i) i
TypeUU i = UU[ Type i , idf (Type i) ]

TypeUU-is-univalent : is-univalent (TypeUU i)
TypeUU-is-univalent =
  is-eq (transport-equiv (idf _)) ua
        (λ e → transport-equiv-idf (ua e) ∙ coe-equiv-β e)
        (λ p → ua-η (ap (idf _) p) ∙ ap-idf p)

module _ (P : SubtypeProp (Type i) j) where
  open SubtypeProp P

  SubtypeUU : UU (lmax (lsucc i) j) i
  SubtypeUU = UU[ Subtype P , fst ]

  SubtypeUU-is-univalent : is-univalent SubtypeUU
  SubtypeUU-is-univalent {X , ϕ} {Y , ψ} = is-eq f g f-g g-f
    where f : X , ϕ == Y , ψ → X ≃ Y
          f = transport-equiv fst
          g : X ≃ Y → X , ϕ == Y , ψ
          g e = Subtype=-out P (ua e)
          f-g : (e : X ≃ Y) → f (g e) == e
          f-g e = transport-equiv-fst (ua e) (prop-has-all-paths-↓ {{level Y}})
                ∙ coe-equiv-β e
          g-f : (p : X , ϕ == Y , ψ) → g (f p) == p
          g-f p = ap (g ∘ f) (pair=-η p)
                ∙ ap g (transport-equiv-fst (fst= p) (snd= p))
                ∙ ap (Subtype=-out P) (ua-η (fst= p))
                ∙ Subtype=-η P p

open import homotopy.FinSet

FinSetUU = SubtypeUU FinSet-prop
FinSetUU-is-univalent = SubtypeUU-is-univalent FinSet-prop

FinSet-n-prop : (n : ℕ) → SubtypeProp Type₀ (lsucc lzero)
fst (FinSet-n-prop n) X = Σ ℕ λ n → Trunc -1 (Fin n == X)
snd (FinSet-n-prop n) X =
  all-paths-is-prop
    λ { (n , ϕ) (m , ψ) →
        pair= (Trunc-rec (λ p → Trunc-rec (λ q → Fin-inj n m (p ∙ ! q)) ψ) ϕ) prop-has-all-paths-↓ }

FinSet-n-UU : (n : ℕ) → UU _ _
FinSet-n-UU n = SubtypeUU (FinSet-n-prop n)

FinSet-n-UU-is-univalent : (n : ℕ) → is-univalent (FinSet-n-UU n)
FinSet-n-UU-is-univalent n = SubtypeUU-is-univalent (FinSet-n-prop n)

BAutUU : (A : Type i) → UU _ _
BAutUU A = SubtypeUU (BAut-prop A)

BAutUU-is-univalent : (A : Type i) → is-univalent (BAutUU A)
BAutUU-is-univalent A = SubtypeUU-is-univalent (BAut-prop A)

FinSet-exp-is-univalent : (n : ℕ) → is-univalent (BAutUU (Fin n))
FinSet-exp-is-univalent n = BAutUU-is-univalent (Fin n)

UFin-is-univalent = FinSetUU-is-univalent
