-- Lambda-Pi tutorial implementation of dependent types

module Main where

open import Library
open import LamPi.AST     using (Decl; printListDecl)
open import LamPi.Parser  using (Err; ok; bad; parseListDecl)
open import Nice          using (nice; unNice; printNiceError)
open import Scope         using (scopeCheck; printScopeError; printDefs)
open import TypeChecker   using (checkDefs; printTypeError)

open ErrorMonad using (fail; ok)
open IOMonad

-- Pipeline:

-- Parse the given text into a list of declarations.

parse : String → IO (List Decl)
parse contents = do
  case parseListDecl true contents of λ where
    (bad cs) → do
      putStrLn "SYNTAX ERROR"
      putStrLn (String.fromList cs)
      exitFailure
    (Err.ok prg) → do
      putStrLn "PARSER PRODUCED:"
      putStrLn (printListDecl prg)
      return prg

-- Preprocess the parsed declarations into a nice form for scope checking.

nicify : List Decl → IO Nice.Defs
nicify prg = do
  case nice prg of λ where
    (fail err) → do
      putStrLn "NICIFIER ERROR"
      -- putStrLn (printListDecl prg)
      -- putStrLn "The nicifier error is:"
      putStrLn (printNiceError err)
      exitFailure
    (ErrorMonad.ok prg') → do
      putStrLn "NICIFIER PRODUCED:"
      putStrLn (printListDecl (unNice prg'))
      return prg'

-- Scope check the nice declarations.

scope : Nice.Defs → IO (∃ Scope.Defs)
scope (n , prg') = do
  case scopeCheck prg' of λ where
    (fail err) → do
      putStrLn "SCOPE ERROR"
      -- putStrLn (printListDecl (unNice (n , prg')))
      -- putStrLn (printListDecl prg)
      -- putStrLn "The scope error is:"
      putStrLn (printScopeError err)
      exitFailure
    (ErrorMonad.ok prg'') → do
      putStrLn "SCOPE CHECKER PRODUCED:"
      putStrLn (printListDecl (unNice (n , printDefs prg'')))
      return (n , prg'')

-- Type check the scope-checked declarations.

type : ∃ Scope.Defs → IO ⊤
type (n , prg'') = do
  case checkDefs prg'' of λ where
    (fail err) → do
      putStrLn "TYPE ERROR"
      -- putStrLn (printListDecl (unNice (n , printDefs prg'')))
      -- putStrLn "The type error is:"
      putStrLn (printTypeError err)
      exitFailure
    (ErrorMonad.ok _) → do
      putStrLn "TYPE CHECKING SUCCESS"

-- Display usage information and exit.

usage : IO ⊤
usage = do
  putStrLn "Usage: lampi <SourceFile>"
  exitFailure

-- Parse command line argument and pass file contents to pipeline.

main : IO ⊤
main = do
  file ∷ [] ← getArgs where _ → usage
  readFiniteFile file >>= parse >>= nicify >>= scope >>= type
