{-# OPTIONS --without-K --rewriting #-}

module Pi+.Coxeter.NonParametrized.ReductionRel where

open import lib.Base
open import lib.types.Nat using (_+_)
open import lib.PathGroupoid

open import Pi+.Misc
open import Pi+.Coxeter.Common.Arithmetic
open import Pi+.Coxeter.Common.ListN

data _≅_ : Listℕ -> Listℕ -> Type₀ where
  cancel≅ : {n : ℕ} -> (l r m mf : Listℕ) -> (defm : m == l ++ n ∷ n ∷ r) -> (defmf : mf == l ++ r) -> (m ≅ mf)
  swap≅ : {n : ℕ} -> {k : ℕ} -> (S k < n) ->  (l r m mf : Listℕ) -> (defm : m == l ++ n ∷ k ∷ r) -> (defmf : mf == l ++ k ∷ n ∷ r) -> (m ≅ mf)
  long≅ : {n : ℕ} -> (k : ℕ) -> (l r m mf : Listℕ) -> (defm : m == l ++ (n ↓ (2 + k)) ++ (1 + k + n) ∷ r) -> (defmf : mf == l ++ (k + n) ∷ (n ↓ (2 + k)) ++ r) -> (m ≅ mf)

data _≅*_ : Listℕ -> Listℕ -> Type₀ where
  idp : {m : Listℕ} -> m ≅* m
  trans≅ : {m1 m2 m3 : Listℕ} -> (m1 ≅ m2) -> (m2 ≅* m3) -> m1 ≅* m3

cancel-c : {n : ℕ} -> (l r : Listℕ) -> (l ++ n ∷ n ∷ r) ≅ (l ++ r)
cancel-c {n} = λ l r → cancel≅ l r (l ++ n ∷ n ∷ r) (l ++ r) idp idp

swap-c : {n : ℕ} -> {k : ℕ} -> (pk : S k < n) ->  (l r : Listℕ) -> (l ++ n ∷ k ∷ r) ≅ (l ++ k ∷ n ∷ r)
swap-c {k} pk l r = swap≅ pk l r (l ++ k ∷ _ ∷ r) (l ++ _ ∷ k ∷ r) idp idp

long-c : {n : ℕ} -> (k : ℕ) -> (l r : Listℕ) -> (l ++ (n ↓ (2 + k)) ++ (1 + k + n) ∷ r) ≅ (l ++ (k + n) ∷ (n ↓ (2 + k)) ++ r)
long-c k l r = long≅ k l r _ _ idp idp

ext : {l l' : Listℕ} -> l ≅ l' -> l ≅* l'
ext p = trans≅ p idp

cancel : {n : ℕ} -> (l r : Listℕ) -> (l ++ n ∷ n ∷ r) ≅* (l ++ r)
cancel {n} = λ l r →
             trans≅ (cancel≅ l r (l ++ n ∷ n ∷ r) (l ++ r) idp idp) idp

swap : {n : ℕ} -> {k : ℕ} -> (pk : S k < n) ->  (l r : Listℕ) -> (l ++ n ∷ k ∷ r) ≅* (l ++ k ∷ n ∷ r)
swap {k} {n} pk l r = trans≅ (swap≅ pk l r (l ++ k ∷ _ ∷ r) (l ++ _ ∷ k ∷ r) idp idp) idp

long : {n : ℕ} -> (k : ℕ) -> (l r : Listℕ) -> (l ++ (n ↓ (2 + k)) ++ (1 + k + n) ∷ r) ≅* (l ++ (k + n) ∷ (n ↓ (2 + k)) ++ r)
long k l r = ext (long≅ k l r _ _ idp idp)

braid : {n : ℕ} -> (l r : Listℕ) -> (l ++ S n ∷ n ∷ S n ∷ r) ≅* (l ++ n ∷ S n ∷ n ∷ r)
braid {n} l r = long {n} 0 l r

trans : {m1 m2 m3 : Listℕ} -> (m1 ≅* m2) -> (m2 ≅* m3) -> m1 ≅* m3
trans idp p  = p
trans (trans≅ x q) p = trans≅ x (trans q p)

l++≅ : (m1 m2 l : Listℕ) -> (m1 ≅ m2) -> ((l ++ m1) ≅ (l ++ m2))
l++≅ m1 m2 l (cancel≅ l₁ r .m1 .m2 defm defmf) =  cancel≅ (l ++ l₁) r _ _ (≡-trans (start+end idp defm) (≡-sym (++-assoc l l₁ _))) ((≡-trans (start+end idp defmf) (≡-sym (++-assoc l l₁ _))))
l++≅ m1 m2 l (swap≅ x l₁ r .m1 .m2 defm defmf) =  swap≅ x (l ++ l₁) r _ _ (≡-trans (start+end idp defm) (≡-sym (++-assoc l l₁ _))) ((≡-trans (start+end idp defmf) (≡-sym (++-assoc l l₁ _))))
l++≅ m1 m2 l (long≅ k l₁ r .m1 .m2 defm defmf) =  long≅ k (l ++ l₁) r _ _ (≡-trans (start+end idp defm) (≡-sym (++-assoc l l₁ _))) ((≡-trans (start+end idp defmf) (≡-sym (++-assoc l l₁ _))))

l++ : (l : Listℕ) -> {m1 m2 : Listℕ} -> (m1 ≅* m2) -> ((l ++ m1) ≅* (l ++ m2))
l++ l idp = idp
l++ l (trans≅ x p) = trans≅ (l++≅ _ _ l x) ((l++ l p))

++r≅ : (m1 m2 r : Listℕ) -> (m1 ≅ m2) -> ((m1 ++ r) ≅ (m2 ++ r))
++r≅ m1 m2 r (cancel≅ l r₁ .m1 .m2 defm defmf) = cancel≅ l (r₁ ++ r)  _ _  (≡-trans (start+end defm idp) (++-assoc l _ r)) ((≡-trans (start+end defmf idp) (++-assoc l _ r)))
++r≅ m1 m2 r (swap≅ x l r₁ .m1 .m2 defm defmf) = swap≅ x l (r₁ ++ r)  _ _  (≡-trans (start+end defm idp) (++-assoc l _ r)) ((≡-trans (start+end defmf idp) (++-assoc l _ r)))
++r≅ m1 m2 r (long≅ k l r₁ .m1 .m2 defm defmf) = long≅ k l (r₁ ++ r)  _ _
  (≡-trans (start+end defm idp) (≡-trans (++-assoc l _ r) (start+end (idp {a = l}) (head+tail idp (head+tail idp (++-assoc (_ ↓ k) _ r))))))
  ((≡-trans (start+end defmf idp) (≡-trans (++-assoc l _ r) (start+end (idp {a = l}) (head+tail idp (head+tail idp (head+tail idp (++-assoc _ r₁ r))))))))

++r : {m1 m2 : Listℕ} -> (r : Listℕ) -> (m1 ≅* m2) -> ((m1 ++ r) ≅* (m2 ++ r))
++r r idp = idp
++r r (trans≅ x p) = trans≅ (++r≅ _ _ r x) (++r r p)

idp≅* : {l l' : Listℕ} -> (l == l') -> l ≅* l'
idp≅* idp = idp

module ≅*-Reasoning where
    infix  1 ≅*begin_
    infixr 2 _≅*⟨⟩_ _≅*⟨_⟩_
    infix  3 _≅*∎

    ≅*begin_ : ∀ {x y : Listℕ}
             → x ≅* y
               -----
             → x ≅* y
    ≅*begin x≅*y  =  x≅*y

    _≅*⟨⟩_ : ∀ (x : Listℕ) {y : Listℕ}
            → x ≅* y
              -----
            → x ≅* y
    x ≅*⟨⟩ x≅*y  =  x≅*y

    _≅*⟨_⟩_ : ∀ (x : Listℕ) {y z : Listℕ}
             → x ≅* y
             → y ≅* z
               -----
             → x ≅* z
    x ≅*⟨ x≅*y ⟩ y≅*z  = trans x≅*y y≅*z

    _≅*∎ : ∀ (x : Listℕ)
           -----
          → x ≅* x
    x ≅*∎  =  idp

open ≅*-Reasoning

≅-abs-l : {x : ℕ} -> (x ∷ nil) ≅ nil -> ⊥
≅-abs-l (cancel≅ nil r .(_ ∷ nil) .nil () defmf)
≅-abs-l (cancel≅ (x ∷ nil) r .(_ ∷ nil) .nil () defmf)
≅-abs-l (cancel≅ (x ∷ x₁ ∷ l) r .(_ ∷ nil) .nil () defmf)
≅-abs-l (swap≅ x nil r .(_ ∷ nil) .nil () defmf)
≅-abs-l (swap≅ x (x₁ ∷ nil) r .(_ ∷ nil) .nil () defmf)
≅-abs-l (swap≅ x (x₁ ∷ x₂ ∷ l) r .(_ ∷ nil) .nil () defmf)
≅-abs-l (long≅ k nil r .(_ ∷ nil) .nil defm ())
≅-abs-l (long≅ k (x ∷ l) r .(_ ∷ nil) .nil defm ())

≅-abs-r : {x : ℕ} -> nil ≅ (x ∷ nil) -> ⊥
≅-abs-r (cancel≅ nil r .nil .(_ ∷ nil) () defmf)
≅-abs-r (cancel≅ (x ∷ l) r .nil .(_ ∷ nil) () defmf)
≅-abs-r (swap≅ x nil r .nil .(_ ∷ nil) () defmf)
≅-abs-r (swap≅ x (x₁ ∷ l) r .nil .(_ ∷ nil) () defmf)
≅-abs-r (long≅ k nil r .nil .(_ ∷ nil) () defmf)
≅-abs-r (long≅ k (x ∷ l) r .nil .(_ ∷ nil) () defmf)
--
empty-reduction : {m : Listℕ} -> (nil ≅ m) -> ⊥
empty-reduction (cancel≅ nil r .nil _ () defmf)
empty-reduction (cancel≅ (x ∷ l) r .nil _ () defmf)
empty-reduction (swap≅ x nil r .nil _ () defmf)
empty-reduction (swap≅ x (x₁ ∷ l) r .nil _ () defmf)
empty-reduction (long≅ k nil r .nil mf () defmf)
empty-reduction (long≅ k (x ∷ l) r .nil mf () defmf)

one-reduction : {x : ℕ} -> {m : Listℕ} -> ([ x ] ≅ m) -> ⊥
one-reduction {x} (cancel≅ (x₁ ∷ nil) r .(x ∷ nil) mf () defmf)
one-reduction {x} (cancel≅ (x₁ ∷ x₂ ∷ l) r .(x ∷ nil) mf () defmf)
one-reduction {x} (swap≅ x₁ (x₂ ∷ nil) r .(x ∷ nil) mf () defmf)
one-reduction {x} (swap≅ x₁ (x₂ ∷ x₃ ∷ l) r .(x ∷ nil) mf () defmf)
one-reduction {x} (long≅ k (x₁ ∷ nil) r .(x ∷ nil) mf () defmf)
one-reduction {x} (long≅ k (x₁ ∷ x₂ ∷ l) r .(x ∷ nil) mf () defmf)