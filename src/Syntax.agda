-- Internal syntax of Lambda-Pi (de Bruijn)

module Syntax where

open import Library

-- Variables are de Bruijn indices
Var = Fin

-- Names are suggestions how to print an index
Name = String

variable
  n m : ℕ

-- Terms

data Tm (n : ℕ) : Set where
  univ : (l : ℕ) → Tm n
  var : (x : Var n) → Tm n
  abs : (y : Name) (t : Tm (suc n)) → Tm n
  app : (t u : Tm n) → Tm n
  pi  : (y : Name) (A : Tm n) (B : Tm (suc n)) → Tm n

-- Substitutions

data Sub (n : ℕ) : ℕ → Set where
  ε : Sub n 0
  _▷_ : (σ : Sub n m) (t : Tm n) → Sub n (suc m)

lookup : Sub n m → Var m → Tm n
lookup ε ()
lookup (σ ▷ t) zero = t
lookup (σ ▷ t) (suc x) = lookup σ x

weakS : (n : ℕ) (m : ℕ) → Sub (n + m) n
weakS zero    m = ε
weakS (suc n) m = weakS n (suc m) ▷ var (Fin.fromℕ n m)

idS : (n : ℕ) → Sub n n
idS n = weakS n zero

sgS : Tm n → Sub n (suc n)
sgS t = idS _ ▷ t

-- performing a substitution

{-# TERMINATING #-}
mutual
  sub : Sub n m → Tm m → Tm n
  sub σ (univ l)   = univ l
  sub σ (var x)    = lookup σ x
  sub σ (abs y t)  = abs y (sub (liftS σ) t)
  sub σ (app t u)  = app (sub σ t) (sub σ u)
  sub σ (pi y A B) = pi y (sub σ A) (sub (liftS σ) B)

  wkS : Sub n m → Sub (suc n) m
  wkS ε = ε
  wkS (σ ▷ t) = wkS σ ▷ wk t

  liftS : Sub n m → Sub (suc n) (suc m)
  liftS σ = wkS σ ▷ var zero

  wk : Tm n → Tm (suc n)
  wk t = sub (weakS _ 1) t

subst1 : Tm n → Tm (suc n) → Tm n
subst1 u = sub (sgS u)

-- weak head normal form

{-# TERMINATING #-}
mutual
  whd : Tm n → Tm n
  whd (app t u) = apply (whd t) u
  whd t = t

  apply : Tm n → Tm n → Tm n
  apply (abs _ t) u = whd (subst1 u t)
  apply t u = app t u
