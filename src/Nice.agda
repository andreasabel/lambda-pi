-- Nicifier: preprocess parsed declarations into snoc list of definitions

module Nice where

open import Library

open import LamPi.AST using (Decl; Block; Ident; Exp)
open Decl
open Block
open Ident

-- Structure returned by nicifier

record Def : Set where
  constructor def
  field
    name : String
    type : Exp
    term : Maybe Exp -- nothing if postulate

Defs = ∃ (Vec Def)

-- Nicifier errors

data NiceError : Set where
  definedPostulate      : String → _
  definitionWithoutType : String → _
  impossible            : _

printNiceError : NiceError → String
printNiceError (definedPostulate x)      = "Postulate with definition: " <> x
printNiceError (definitionWithoutType x) = "Definition without type: " <> x
printNiceError impossible                = "Panic! Internal error"

-- Nicifier monad

open ErrorMonad {E = NiceError} public using () renaming (Error to Nice)

-- Nicifier implementation

private
  open ErrorMonad {E = NiceError} using (fail; return; _>>=_; _>=>_)

  variable
    n : ℕ

  -- Helpers

  addPostulate : String → Exp → Defs → Defs
  addPostulate x e (n , v) = (suc n , def x e nothing ∷ v)

  addDefinition : String → Exp → Exp → Defs → Defs
  addDefinition x e f (n , v) = (suc n , def x e (just f) ∷ v)

  abs : List Ident → Exp → Exp
  abs [] e = e
  abs xs e = Exp.eAbs xs e

  -- Nicifier main loop

  mutual

    -- Process a file

    group : List Decl → Defs → Nice Defs
    group []                            = return
    group (dAx (block ds') ∷ ds)        = postulates ds' >=> group ds
    group (dDecl (ident x) e ∷ ds)      = declaration x e ds
    group (dDef (ident x ∷ _) e ∷ ds) _ = fail (definitionWithoutType x)
    group (dDef []            e ∷ ds) _ = fail impossible

    -- Process a group of postulates

    postulates : List Decl → Defs → Nice Defs
    postulates []                            = return
    postulates (dAx (block ds') ∷ ds)        = postulates ds' >=> postulates ds
    postulates (dDecl (ident x) e ∷ ds)      = postulates ds ∘ addPostulate x e
    postulates (dDef (ident x ∷ _) e ∷ ds) _ = fail (definedPostulate x)
    postulates (dDef []            e ∷ ds) _ = fail impossible

    -- Process the statement after a given declaration

    declaration : (x : String) (e : Exp) (ds : List Decl) → Defs → Nice Defs
    declaration x e (dDef (ident y ∷ ys) f ∷ ds) with x String.≟ y
    ... | yes _ = group ds ∘ addDefinition x e (abs ys f)
    ... | no _  = λ _ → fail (definitionWithoutType y)
    declaration x e (dDef [] f ∷ ds) _ = fail impossible
    declaration x e ds = group ds ∘ addPostulate x e

-- Nicifier entrypoint

nice : List Decl → Nice Defs
nice ds = group ds (0 , [])

-- Converting nice syntax back to parsed syntax

unNiceDef : Def → List Decl
unNiceDef (def x e (just f)) = dDecl (ident x) e ∷ dDef [ ident x ] f ∷ []
unNiceDef (def x e nothing) = [ dAx (block [ dDecl (ident x) e ]) ]

unNice : Defs → List Decl
unNice (_ , v) = Vec.foldl (λ _ → List Decl) (λ ds d → unNiceDef d ++ ds) [] v
