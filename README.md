LamPi - A tutorial implementation of dependent types in Agda
============================================================

This is one of many bidirectional type-checkers for a core dependently typed functional language,
λΠ, written in Agda, using BNFC to generate the parser.

The language is the λ-calculus with dependent function types `(x : A) → B`
and a predicative cumulative hierachy of universes `Set`_n_.

A file is a sequence of declarations of the forms `x : A` (type signature) and
`x ys = e` (definition) where `e` and `A` are expressions.
Definitions must be immediately preceded by their type signature.

The syntax is a subset of Agda's syntax.
`postulate` blocks are also supported.

For an example of the syntax, see [nat.agda](examples/nat.agda).

LamPi can be build by calling `make`.

Prerequisites:
- Stack and GHC
- BNFC
- Agda
- Agda standard library
