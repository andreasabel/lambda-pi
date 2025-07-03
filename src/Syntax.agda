-- Internal syntax of Lambda-Pi (de Bruijn).

module Syntax where

open import Library

-- Variables are de Bruijn indices.
Var = Fin

-- Names are suggestions how to print an index.
Name = String

-- Universe levels are natural numbers.
Lvl = ℕ

variable
  n m : ℕ

-- Terms indexed by the number of variables that may occur.

data Tm (n : ℕ) : Set where
  univ : (l : Lvl) → Tm n
  var  : (x : Var n) → Tm n
  abs  : (y : Name) (t : Tm (suc n)) → Tm n
  app  : (t u : Tm n) → Tm n
  pi   : (y : Name) (A : Tm n) (B : Tm (suc n)) → Tm n

-- Substitutions from terms over m variables to terms over n variables.

data Sub : (n m : ℕ) → Set where

  -- Base: a weakening, serves also as empty and identity substitution.
  baseS : (n : ℕ) → Sub (n + m) m

  -- Lifting a substitution under a binder.
  liftS : (σ : Sub n m) → Sub (suc n) (suc m)

  -- Extending the substitution by a replacement for the 0th variable.
  _▷_   : (σ : Sub n m) (t : Tm n) → Sub n (suc m)

-- Empty substitution.

ε : Sub (n + 0) 0
ε = baseS _

-- Identity substitution.

idS : Sub n n
idS = baseS _

-- Singleton substitution for the 0th variable.

sgS : Tm n → Sub n (suc n)
sgS t = idS ▷ t

-- Substitution and weaking.

-- We are lazy and implement a version that Agda does not recognize terminating.
{-# TERMINATING #-}
mutual

  -- Applying a substitution to a term, performing the replacements.

  sub : Sub n m → Tm m → Tm n
  sub σ (univ l)   = univ l
  sub σ (var x)    = lookup σ x
  sub σ (abs y t)  = abs y (sub (liftS σ) t)
  sub σ (app t u)  = app (sub σ t) (sub σ u)
  sub σ (pi y A B) = pi y (sub σ A) (sub (liftS σ) B)

  -- Looking up a term in a substitution.

  lookup : Sub n m → Var m → Tm n
  lookup (baseS n) x       = var (n Fin.↑ʳ x)
  lookup (liftS σ) zero    = var zero
  lookup (liftS σ) (suc x) = wk (lookup σ x)
  lookup (σ ▷ t)   zero    = t
  lookup (σ ▷ t)   (suc x) = lookup σ x

  -- Weaking a term by 1.

  wk : Tm n → Tm (suc n)
  wk t = sub (baseS _) t

-- Weakening (every term in) a substitution by 1.

wkS : Sub n m → Sub (suc n) m
wkS (baseS n) = baseS (suc n)
wkS (liftS σ) = liftS (wkS σ)
wkS (σ ▷ t)   = wkS σ ▷ wk t

-- Substituting just the 0th variable, dropping the other indices by 1.

subst1 : Tm n → Tm (suc n) → Tm n
subst1 u = sub (sgS u)

-- Weak head normal form.

-- The termination proof (for well-typed terms) is by a logical relation.
-- Does not terminate for all untyped terms.

{-# TERMINATING #-}
mutual
  whnf : Tm n → Tm n
  whnf (app t u) = apply (whnf t) u
  whnf t = t

  apply : Tm n → Tm n → Tm n
  apply (abs _ t) u = whnf (subst1 u t)
  apply t u = app t u
