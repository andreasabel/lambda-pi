-- Translate parsed syntax into de Bruijn syntax

module Scope where

open import Library
open import Data.String using (_≟_)

Name = String

open import LamPi.AST as AST using (Exp; Ident); open Exp; open Ident
open import Syntax using (Tm; Var; wk); open Tm
import Nice

variable
  n : ℕ

record Def (n : ℕ) : Set where
  constructor def
  field
    name : String
    type : Tm n
    term : Maybe (Tm n)

data Defs : (n : ℕ) → Set where
  ε : Defs 0
  _▷_ : Defs n → Def n → Defs (suc n)

data ScopeError : Set where
  notInScope  : String → _
  notUniverse : String → _

printScopeError : ScopeError → String
printScopeError (notInScope x)  = "Not in scope: " <> x
printScopeError (notUniverse x) = "Not a valid universe: " <> x

open ErrorMonad {E = ScopeError} public using () renaming (Error to Scope)
open ErrorMonad {E = ScopeError} using (Error; fail; return; _>>=_; _>=>_; _=<<_; _<$>_; liftM2)

-- Helper: parse a universe level (decimal number)

parseUniv : String → Scope ℕ
parseUniv "Set" = return 0
parseUniv s  = case ℕ.readMaybe 10 (String.drop 3 s) of λ where
  nothing  → fail (notUniverse s)
  (just n) → return n

-- Definitions to context (just their names)

Cxt = Vec Name

cxt : Defs n → Cxt n
cxt ε = []
cxt (ds ▷ def x _ _) = x ∷ cxt ds

-- Lookup an identifier in the context

lookup : String → Cxt n → Scope (Var n)
lookup x [] = fail (notInScope x)
lookup x (y ∷ Δ) with x ≟ y
... | yes _ = return zero
... | no _  = suc <$> lookup x Δ

-- Scope check an expression and return a de Bruijn term

scopeExp : Exp → Cxt n → Scope (Tm n)
scopeExp (eType (AST.univ x)) Δ = univ <$> parseUniv x
scopeExp (eId (ident x))      Δ = var <$> lookup x Δ
scopeExp (eApp e f)           Δ = liftM2 app (scopeExp e Δ) (scopeExp f Δ)
scopeExp (eFun A B)           Δ = liftM2 (pi "_") (scopeExp A Δ) (wk <$> scopeExp B Δ)
scopeExp (ePi (ident x) A B)  Δ = liftM2 (pi x) (scopeExp A Δ) (scopeExp B (x ∷ Δ))
scopeExp (eAbs xs e)          Δ = scopeAbs xs e Δ
  where
  scopeAbs : (xs : List Ident) (e : Exp) (Δ : Cxt n) → Scope (Tm n)
  scopeAbs []             e Δ = scopeExp e Δ
  scopeAbs (ident x ∷ xs) e Δ = abs x <$> scopeAbs xs e (x ∷ Δ)

scopeMaybeExp : Maybe Exp → Cxt n → Scope (Maybe (Tm n))
scopeMaybeExp (just e) Δ = just <$> scopeExp e Δ
scopeMaybeExp nothing  Δ = return nothing

-- Scope check a definition

scopeDef : Nice.Def → Defs n → Scope (Defs (suc n))
scopeDef (Nice.def x e m) ds = (ds ▷_) <$> liftM2 (def x) (scopeExp e Δ) (scopeMaybeExp m Δ)
  where Δ = cxt ds

-- Scope check a file

scopeCheck : Vec Nice.Def n → Scope (Defs n)
scopeCheck [] = return ε
scopeCheck (d ∷ ds) = scopeDef d =<< scopeCheck ds
