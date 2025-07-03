-- Translate parsed syntax into de Bruijn syntax

module Scope where

open import Library

open import LamPi.AST as AST using (Exp; Ident); open Exp; open Ident
open import Syntax using (Name; Tm; Var; wk); open Tm
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
  impossible  : _

printScopeError : ScopeError → String
printScopeError (notInScope x)  = "Not in scope: " <> x
printScopeError (notUniverse x) = "Not a valid universe: " <> x
printScopeError impossible      = "Panic! Internal error"

open ErrorMonad {E = ScopeError} public using () renaming (Error to Scope)
open ErrorMonad {E = ScopeError} using (fail; return; _>>=_; _>=>_; _=<<_; _<$>_; liftM2)

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
lookup x (y ∷ Δ) with x String.≟ y
... | yes _ = return zero
... | no _  = suc <$> lookup x Δ

-- Scope check an expression and return a de Bruijn term

scopeExp : Exp → Cxt n → Scope (Tm n)
scopeExp (eType (AST.univ x))     Δ = univ <$> parseUniv x
scopeExp (eId (ident x))          Δ = var <$> lookup x Δ
scopeExp (eApp e f)               Δ = liftM2 app (scopeExp e Δ) (scopeExp f Δ)
scopeExp (eFun A B)               Δ = liftM2 (pi "_") (scopeExp A Δ) (scopeExp B ("_" ∷ Δ))
scopeExp (ePi [] A B)             Δ = fail impossible
scopeExp (ePi (ident x ∷ xs) A B) Δ = scopePi Δ x xs =<< scopeExp A Δ
  where
  scopePi : Cxt n → String → List Ident → Tm n → Scope (Tm n)
  scopePi Δ x []             A = pi x A <$> scopeExp B (x ∷ Δ)
  scopePi Δ x (ident y ∷ ys) A = pi x A <$> scopePi (x ∷ Δ) y ys (wk A)
scopeExp (eAbs xs e) Δ = scopeAbs xs e Δ
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

------------------------------------------------------------------------
-- Printing (unscope)

printTm : Cxt n → Tm n → Exp
printTm Δ (univ 0)   = eType (AST.univ ("Set"))
printTm Δ (univ l)   = eType (AST.univ ("Set" <> printNat l))
printTm Δ (var x)    = eId (ident (Vec.lookup Δ x))
printTm Δ (abs y t)  = eAbs [ ident y ] (printTm (y ∷ Δ) t) -- todo: freshen y
printTm Δ (app t u)  = eApp (printTm Δ t) (printTm Δ u)
printTm Δ (pi y A B) = ePi [ ident y ] (printTm Δ A) (printTm (y ∷ Δ) B) -- todo: freshen y

printDef : Cxt n → Def n → Nice.Def
printDef Δ (def x type term) = Nice.def x (printTm Δ type) (Maybe.map (printTm Δ) term)

printDefs : Defs n → Vec Nice.Def n
printDefs ε = []
printDefs (ds ▷ d) = printDef (cxt ds) d ∷ printDefs ds
