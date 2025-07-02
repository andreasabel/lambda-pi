-- Type check definitions bidirectionally

module TypeChecker where

open import Library
open import Syntax hiding (lookup)
open import Scope as A using (Def; Defs; cxt; printTm)
open import LamPi.AST as AST using (Exp; printExp)

data TypeError : Set where
  notAType     : Exp → _
  notAUniverse : Exp → _
  notAFunction : Exp → Exp → _
  notAFunType  : Exp → _
  notInferable : Exp → _
  notLeqLevels : Lvl → Lvl → _
  notSubtype   : Exp → Exp → _

printTypeError : TypeError → String
printTypeError (notAType e)       = "Not a type: " <> printExp e
printTypeError (notAUniverse e)   = "Not a universe: " <> printExp e
printTypeError (notAFunType A)    = "Not a function type: " <> printExp A
printTypeError (notAFunction e A) = printExp e <> " has type " <> printExp A <> " but is expected to be of function type"
printTypeError (notInferable e)   = "Not an inferable term: " <> printExp e
printTypeError (notLeqLevels l l') = "Level " <> printNat l <> " is not less or equal to " <> printNat l'
printTypeError (notSubtype A B)   = printExp A <> " is not a subtype of " <> printExp B

open ErrorMonad {E = TypeError} public using () renaming (Error to TC)
open ErrorMonad {E = TypeError} using (fail; return; _>>=_; _>>_; _>=>_; _=<<_; _<$>_; liftM2)

-- Type error "not a type"

notType : ∀{A : Set} → Defs n → Tm n → TC A
notType Σ t = fail (notAType (printTm (cxt Σ) t))

-- Type error "not a universe"

notUniverse : ∀{A : Set} → Defs n → Tm n → TC A
notUniverse Σ t = fail (notAUniverse (printTm (cxt Σ) t))

-- Type error "not a function type"

notFunctionType : ∀{A : Set} → Defs n → Tm n → TC A
notFunctionType Σ t = fail (notAFunType (printTm (cxt Σ) t))

-- Type error "not a function"

notFunction : ∀{A : Set} → Defs n → Tm n → Tm n → TC A
notFunction Σ t A = fail (notAFunction (printTm Δ t) (printTm Δ A))
  where
    Δ = cxt Σ

-- Type error "not inferable"

cannotInfer : ∀{A : Set} → Defs n → Tm n → TC A
cannotInfer Σ t = fail (notInferable (printTm (cxt Σ) t))

-- Equality error "not subtype

notSubtypes : ∀{A : Set} → Defs n → Tm n → Tm n → TC A
notSubtypes Σ A B = fail (notSubtype (printTm Δ A) (printTm Δ B))
  where
    Δ = cxt Σ

-- Turn a definition into a term formally depending on itself
-- (the latter case is necessary for axioms, they are defined as themselves).

toTm : Def n → Tm (suc n)
toTm (A.def _ _ (just t)) = wk t
toTm (A.def _ _ nothing) = var zero

-- Turn already independent defs into a substitution

toSubst : Defs n → Sub n n
toSubst Defs.ε = ε
toSubst (Σ Defs.▷ d) = wkS (toSubst Σ) ▷ toTm d

-- toTm : Sub n n → Def n → Tm (suc n)
-- toTm σ (A.def _ _ (just t)) = wk (sub σ t)
-- toTm σ (A.def _ _ nothing) = var zero

-- toSubst : Defs n → Sub n n
-- toSubst Defs.ε = ε
-- toSubst (Σ Defs.▷ d) = wkS σ ▷ toTm σ d
--   where
--     σ = toSubst Σ

-- Close a def wrt. an already flattened list of defs

closeDef : Defs n → Def n → Def n
closeDef Σ (A.def x A m) = A.def x (sub σ A) (Maybe.map (sub σ) m)
  where
    σ = toSubst Σ

-- -- Transform a list of definitions such that each is independent of the previous ones

-- flatten : Defs n → Defs n
-- flatten Defs.ε        = Defs.ε
-- flatten (ds Defs.▷ d) = Σ Defs.▷ closeDef Σ d
--   where
--     Σ = flatten ds

-- Replace in a term all defined things by their definition.
-- Precondition: Σ is already flattened.

close : Defs n → Tm n → Tm n
close Σ = sub (toSubst Σ)

-- Extend a (flattened) context by a new entry.

ext : Defs n → Name → Tm n → Defs (suc n)
ext Σ x A = Σ A.▷ A.def x A nothing

-- Lookup the type of a variable in the context.

lookupType : (Σ : Defs n) (x : Var n) → TC (Tm n)
lookupType Defs.ε ()
lookupType (Σ Defs.▷ A.def _ A _) zero = return $ wk A
lookupType (Σ Defs.▷ _) (suc x) = wk <$> lookupType Σ x

---------------------------------------------------------------------------
-- Subtyping / equality

-- Level subsumption

leqLevel : (l l' : Lvl) → TC ⊤
leqLevel l l' with l ℕ.≤? l'
... | yes _ = return _
... | no _  = fail (notLeqLevels l l')

{-# TERMINATING #-}
mutual
  -- Check subsumption of whnfs
  subType : (Σ : Defs n) (A B : Tm n) → TC ⊤
  subType Σ (univ l) (univ l') = leqLevel l l'
  subType Σ A@(univ _) B         = notSubtypes Σ A B
  subType Σ A        B@(univ _)  = notSubtypes Σ A B
  subType Σ (pi x A B) (pi x' A' B') = do
        subType Σ (whnf A') (whnf A)
        subType (ext Σ x' A') (whnf B) (whnf B')
  subType Σ A@(pi _ _ _) B = notSubtypes Σ A B
  subType Σ A B@(pi _ _ _) = notSubtypes Σ A B
  subType Σ A B = do
    _ ← equalInferable Σ A B
    return _
    -- where
    --   notSubtypes Σ A B : TC ⊤
    --   notSubtypes Σ A B = {!!}

  -- isUniv : Defs n → Tm n → TC Lvl
  -- isUniv Σ A = case whnf A of λ where
  --   (univ l) → return l
  --   _ → notUniverse Σ A

  equalInferable : (Σ : Defs n) (A B : Tm n) → TC (Tm n)
  equalInferable Σ A B = TODO
    where
      TODO = return A

---------------------------------------------------------------------------
-- Checking terms and types

mutual
  -- Check a type and infer its universe level

  checkType : Defs n → Tm n → TC Lvl
  checkType Σ (univ l)    = return (suc l)
  checkType Σ t@(var _)   = inferType Σ t
  checkType Σ t@(abs _ _) = notType Σ t
  checkType Σ t@(app _ _) = inferType Σ t
  checkType Σ (pi y A B)  = checkPiType Σ y A B

  checkPiType : Defs n → Name → Tm n → Tm (suc n) → TC Lvl
  checkPiType Σ y A B = do
    lA ← checkType Σ A
    -- Since A enters the context, it needs to evaluate,
    -- so we close it.
    lB ← checkType (ext Σ y (close Σ A)) B
    return (lA ℕ.⊔ lB)

  -- Infer a neutral and interpret it as type.

  inferType : Defs n → Tm n → TC Lvl
  inferType Σ t = do
    univ l ← whnf <$> infer Σ t where _ → notType Σ t
    return l

  -- Infer type of a neutral term.

  infer : Defs n → Tm n → TC (Tm n)
  infer Σ (univ l) = return (univ (suc l))
  infer Σ (var x) = lookupType Σ x
  infer Σ t@(abs _ _) = cannotInfer Σ t
  infer Σ (app t u) = do
    pi x A B ← whnf <$> infer Σ t
      where C → notFunction Σ t C
    check Σ u A
    -- Since u becomes part of a type, it should evaluate,
    -- so we need close it under the definitions.
    return (subst1 (close Σ u) B)
  infer Σ (pi y A B) = univ <$> checkPiType Σ y A B

  check : (Σ : Defs n) (t : Tm n) (C : Tm n) → TC ⊤
  check Σ (abs y t) C = case whnf C of λ where
    (pi x A B) → check (ext Σ y A) t B  -- need not close A as it is already
    _ → notFunctionType Σ C
  check Σ t C = checkInferable Σ t C
  -- check Σ (univ l) A = do
  --   l' ← isUniv Σ A
  --   leqLevel (suc l) l'
  -- check Σ t@(var _)   A = {!!}
  -- check Σ t@(app _ _) A = {!!}
  -- check Σ (pi y A B) U = do
  --   l' ← isUniv Σ U
  --   l  ← checkPiType Σ y A B
  --   leqLevel l l'

  checkInferable : (Σ : Defs n) (t : Tm n) (A : Tm n) → TC ⊤
  checkInferable Σ t B = do
    A ← infer Σ t
    subType Σ (whnf A) (whnf B)

---------------------------------------------------------------------------
-- Checking definitions

-- Check a definition and return its closed form
checkDef : Defs n → Def n → TC (Def n)
checkDef Σ (A.def x A nothing) = do
  _ ← checkType Σ A
  return (A.def x (close Σ A) nothing)
checkDef Σ (A.def x A (just t)) = do
  _ ← checkType Σ A
  let A' = close Σ A
  check Σ t A'
  return (A.def x A' (just (close Σ t)))

-- Check definitions and flatten them
checkDefs : Defs n → TC (Defs n)
checkDefs Defs.ε = return Defs.ε
checkDefs (ds Defs.▷ d) = do
  Σ ← checkDefs ds
  (Σ Defs.▷_) <$> checkDef Σ d
