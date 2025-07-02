
Nat : Set1
Nat = (A : Set0) → (A → A) → (A → A)

zero : Nat
zero = λ A s z → z

suc : Nat → Nat
suc = λ n A s z → s (n A s z)

plus : Nat → Nat → Nat
plus = λ n m A s z → n A s (m A s z)

times : Nat → Nat → Nat
times = λ n m A s → n A (m A s)
