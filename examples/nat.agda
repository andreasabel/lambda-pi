
-- Equality for large types like Nat

Eq : (A : Set1) → (t : A) → (t' : A) → Set1
Eq = λ A t t' → (P : A → Set) → P t → P t'

sym : (A : Set1) → (r : A) → (s : A) → Eq A r s → Eq A s r
sym = λ A r s rs P ps → rs (λ x → P x → P r) (λ pr → pr) ps

refl : (A : Set1) → (t : A) → Eq A t t
refl = λ A t P pt → pt

trans : (A : Set1) → (r : A) → (s : A) → (t : A) → Eq A r s → Eq A s t → Eq A r t
trans = λ A r s t rs st P pr → st P (rs P pr)

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

-- Laws

-- plus is monoid

plus_zero_left : (n : Nat) → Eq Nat (plus zero n) n
plus_zero_left = refl Nat

plus_zero_right : (n : Nat) → Eq Nat (plus n zero) n
plus_zero_right = refl Nat

plus_assoc : (n : Nat) → (m : Nat) → (l : Nat) → Eq Nat (plus (plus n m) l) (plus n (plus m l))
plus_assoc = λ n m l → refl Nat (plus n (plus m l))

-- times is monoid

one : Nat
one = suc zero

times_one_left : (n : Nat) → Eq Nat (times one n) n
times_one_left = refl Nat

times_one_right : (n : Nat) → Eq Nat (times n one) n
times_one_right = refl Nat

times_assoc : (n : Nat) → (m : Nat) → (l : Nat) → Eq Nat (times (times n m) l) (times n (times m l))
times_assoc = λ n m l → refl Nat (times n (times m l))

-- zero is annihilating

times_zero_left : (n : Nat) → Eq Nat (times zero n) zero
times_zero_left = λ n → refl Nat zero

-- Not provable
-- times_zero_right : (n : Nat) → Eq Nat (times n zero) zero
-- times_zero_right = λ n → refl Nat zero
