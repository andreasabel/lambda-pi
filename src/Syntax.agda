-- Internal syntax of Lambda-Pi (de Bruijn)

module Syntax where

open import Library

-- Variables are de Bruijn indices
Var = Fin

-- Names are suggestions how to print an index
Name = String

-- Universe levels are natural numbers
Lvl = ℕ

variable
  n m : ℕ

-- Terms

data Tm (n : ℕ) : Set where
  univ : (l : Lvl) → Tm n
  var : (x : Var n) → Tm n
  abs : (y : Name) (t : Tm (suc n)) → Tm n
  app : (t u : Tm n) → Tm n
  pi  : (y : Name) (A : Tm n) (B : Tm (suc n)) → Tm n

-- Substitutions

data Sub : (n m : ℕ) → Set where
  ε     : Sub n 0
  idS   : Sub n n
  baseS : (n : ℕ) → Sub (n + m) m
  liftS : (σ : Sub n m) → Sub (suc n) (suc m)
  _▷_   : (σ : Sub n m) (t : Tm n) → Sub n (suc m)

-- -- Wrong:
-- weakS : (n : ℕ) (m : ℕ) → Sub (n + m) n
-- weakS zero    m = ε
-- weakS (suc n) m = weakS n (suc m) ▷ var (Fin.fromℕ n m)


-- performing a substitution

{-# TERMINATING #-}
mutual

  lookup : Sub n m → Var m → Tm n
  lookup ε ()
  lookup idS       x       = var x
  lookup (baseS n) x       = var (n Fin.↑ʳ x)
  lookup (liftS σ) zero    = var zero
  lookup (liftS σ) (suc x) = wk (lookup σ x)
  lookup (σ ▷ t)   zero    = t
  lookup (σ ▷ t)   (suc x) = lookup σ x

  sub : Sub n m → Tm m → Tm n
  sub σ (univ l)   = univ l
  sub σ (var x)    = lookup σ x
  sub σ (abs y t)  = abs y (sub (liftS σ) t)
  sub σ (app t u)  = app (sub σ t) (sub σ u)
  sub σ (pi y A B) = pi y (sub σ A) (sub (liftS σ) B)

  -- liftS : Sub n m → Sub (suc n) (suc m)
  -- liftS σ = wkS σ ▷ var zero

  wk : Tm n → Tm (suc n)
  wk t = sub (baseS _) t

  -- idS : (n : ℕ) → Sub n n
  -- idS zero = ε
  -- idS (suc n) = wkS (idS n) ▷ var zero

wkS : Sub n m → Sub (suc n) m
wkS idS = baseS _
wkS (baseS n) = baseS _
wkS (liftS σ) = liftS (wkS σ)
wkS ε = ε
wkS (σ ▷ t) = wkS σ ▷ wk t

sgS : Tm n → Sub n (suc n)
sgS t = idS ▷ t

subst1 : Tm n → Tm (suc n) → Tm n
subst1 u = sub (sgS u)

-- weak head normal form

{-# TERMINATING #-}
mutual
  whnf : Tm n → Tm n
  whnf (app t u) = apply (whnf t) u
  whnf t = t

  apply : Tm n → Tm n → Tm n
  apply (abs _ t) u = whnf (subst1 u t)
  apply t u = app t u

-- -}
