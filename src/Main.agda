module Main where

open import Library
open import LamPi.AST     using (Decl; printListDecl)
open import LamPi.Parser  using (Err; ok; bad; parseListDecl)
-- open import TypeChecker   using (printError; module CheckDecl)

check : String → IO ⊤
check contents = do
  case parseListDecl true contents of λ where
    (bad cs) → do
      putStrLn "SYNTAX ERROR"
      putStrLn (String.fromList cs)
      exitFailure
    (Err.ok prg) → do
      putStrLn (printListDecl prg)
      -- case checkDecl prg of λ where
      --   (fail err) → do
      --     putStrLn "TYPE ERROR"
      --     putStrLn (printListDecl prg)
      --     putStrLn "The type error is:"
      --     putStrLn (printError err)
      --     exitFailure
      --   (ErrorMonad.ok (Σ , _ , prg')) → do
      --     runDecl prg'

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
