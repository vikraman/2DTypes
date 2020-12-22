

FSMG A = [] | cons | swap | swap^2 | hexagon

swap : x :: y :: xs == y :: x :: xs

swap^2 : swap x y xs ∙ swap y x xs == idp

hexagon : the two swap paths (x :: y :: z :: xs == z :: y :: x :: xs)  are equal


[1, 2, 3, 4] == [2, 1, 4, 3]

(1 2) (3 4)

(3 4) (1 2)

(swap(1,2,[3,4])) ∙ ap (2 :: 1 :: _) swap(3, 4, [])

(ap (1 :: 2 :: _) swap(3, 4, [])) ∙ swap(1,2,[3,4])

p ∙ ap f q == ap f' q ∙ p


[1,2,3,4] == [2,1,3,4] : swap(1,2,[3,4])
[2,1,3,4] == [2,1,4,3] : ap (2 :: 1 :: _) swap(3, 4, [])

==

[1,2,3,4] == [1,2,4,3] : ap (1 :: 2 :: _) swap(3, 4, [])
[1,2,3,4] == [2,1,3,4] : swap(1,2,[3,4])



We can prove:

- ⊗ : FSMG A -> FSMG A -> FSMG A
- A ⊗ B == B ⊗ A
- [] ⊗ A == A ⊗ [] == A
- assoc, pentagon, hexagon for ⊗

FSMG Nat

[1,2,3] == [2,1,3] : FSMG Nat

- FSMG has a universal property.

- When we know UFin has ∪ with unit, comm, assoc, pentagon, hexagon, we get the map
  FSMG 1 -> UFin, which is a symmetric monoidal functor by univ. propery.

- Can we prove Ufin -> FSMG 1 ?

Ufin = Σ n. Fin(n) quotiented by symmetries of Sn
FSMG 1 = Free Symmetric monoidal groupoid on one generator

Path space of FSMG 1 ≃ Σ n. (Fin(n) ≃ Fin(n)) ?

(Fin(n) ≃ Fin(n)) -> coherent 1-path in FSMG



---


pp1 = ap2 _⊗_ β (ap2 _⊗_ idp)
pp2 = ap2 _⊗_ (ap2 _⊗_ idp) β

pp1 ∙ pp2 == pp2 ∙ pp1