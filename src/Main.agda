module Main where

open import Library
open import LamPi.AST     using (Decl; printListDecl)
open import LamPi.Parser  using (Err; ok; bad; parseListDecl)
open import Nice as _     using (Nice; nice; unNice; printNiceError)
open import Scope as _    using (Scope; scopeCheck; printScopeError; printDefs)
open import TypeChecker   using (checkDefs; printTypeError)

check : String → IO ⊤
check contents = do
  case parseListDecl true contents of λ where
    (bad cs) → do
      putStrLn "SYNTAX ERROR"
      putStrLn (String.fromList cs)
      exitFailure
    (Err.ok prg) → do
      case nice prg of λ where
        (fail err) → do
          putStrLn "NICIFIER ERROR"
          putStrLn (printListDecl prg)
          putStrLn "The nicifier error is:"
          putStrLn (printNiceError err)
          exitFailure
        (ErrorMonad.ok (n , prg')) → do
          putStrLn "NICIFIER PRODUCED:"
          putStrLn (printListDecl (unNice (n , prg')))
          case scopeCheck prg' of λ where
            (fail err) → do
              putStrLn "SCOPE ERROR"
              putStrLn (printListDecl (unNice (n , prg')))
              -- putStrLn (printListDecl prg)
              putStrLn "The scope error is:"
              putStrLn (printScopeError err)
              exitFailure
            (ErrorMonad.ok prg'') → do
              putStrLn "SCOPE CHECKER PRODUCED:"
              putStrLn (printListDecl (unNice (n , printDefs prg'')))
              case checkDefs prg'' of λ where
                (fail err) → do
                  putStrLn "TYPE ERROR"
                  putStrLn (printListDecl (unNice (n , printDefs prg'')))
                  putStrLn "The type error is:"
                  putStrLn (printTypeError err)
                  exitFailure
                (ErrorMonad.ok _) → do
                  putStrLn "TYPE CHECKING SUCCESS"
                  -- putStrLn (printListDecl (unNice (n , printDefs prg'')))
                  -- putStrLn "SUCCESS"

  where
  open IOMonad
  -- open CheckDecl using (checkDecl)
  open ErrorMonad using (fail; ok)

-- Display usage information and exit

usage : IO ⊤
usage = do
  putStrLn "Usage: lampi <SourceFile>"
  exitFailure
  where open IOMonad

-- Parse command line argument and pass file contents to check.

main : IO ⊤
main = do
  file ∷ [] ← getArgs where _ → usage
  check =<< readFiniteFile file
  where open IOMonad
