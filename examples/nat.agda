
-- Church natural numbers

Nat : Set1
Nat = (A : Set) → (A → A) → (A → A)

zero : Nat
zero = λ A s z → z

suc : Nat → Nat
suc = λ n A s z → s (n A s z)

plus : Nat → Nat → Nat
plus = λ n m A s z → n A s (m A s z)

times : Nat → Nat → Nat
times = λ n m A s → n A (m A s)

-- Equality for large types like Nat

Eq : (A : Set1) → (t : A) → (t' : A) → Set1
Eq = λ A t t' → (P : A → Set) → P t → P t'

sym : (A : Set1) → (r : A) → (s : A) → Eq A r s → Eq A s r
sym = λ A r s rs P ps → rs (λ x → P x → P r) (λ pr → pr) ps

refl : (A : Set1) → (t : A) → Eq A t t
refl = λ A t P pt → pt

trans : (A : Set1) → (r : A) → (s : A) → (t : A) → Eq A r s → Eq A s t → Eq A r t
trans = λ A r s t rs st P pr → st P (rs P pr)
