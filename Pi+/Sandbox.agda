_↓_ : (n : ) -> (k : ℕ) -> C n
n ↓ 0 = nilC
n ↓ (S k) = (k + n) :: (n ↓ k)

postulate
    nilC : C n
    _::_ : (k : Fin n) → C n → C n
    
    cancel : ∀ (x : Fin n) -> (xs : C n) → xs == (x ↓ 1 :: (x ↓ 1 :: xs))
    swap : ∀ (x y : Fin n) -> (zs : C n) → (S (x .fst) < y .fst) → (y ↓ 1 :: (x ↓ 1 :: zs)) == (x ↓ 1 :: (y ↓ 1 :: zs))
    -- long : ∀ x y zs → (x ↓ (S y) :: ((S x) ↓ 1 :: zs)) == (x ↓ 1 :: (x ↓ S y :: zs))

TT n = List (Fin n)

postulate
    enList : List (Fin n) -> C n
    
    cancel : ∀ (x : Fin n) -> (xs : C n) → xs == (x ↓ 1 :: (x ↓ 1 :: xs))
    swap : ∀ (x y : Fin n) -> (zs : C n) → (S (x .fst) < y .fst) → (y ↓ 1 :: (x ↓ 1 :: zs)) == (x ↓ 1 :: (y ↓ 1 :: zs))
    -- long : ∀ x y zs → (x ↓ (S y) :: ((S x) ↓ 1 :: zs)) == (x ↓ 1 :: (x ↓ S y :: zs))


code : ℕ -> Type
code 0 = ⊤
code (S n) = ⊥

f : 0 == 1 -> ⊥
f p = transport code p tt