------------------------------------------------------------------------
-- Examples involving simple λ-calculi
------------------------------------------------------------------------

{-# OPTIONS --cubical --sized-types #-}

module README.Lambda where

------------------------------------------------------------------------
-- An untyped λ-calculus with constants

-- Some developments from "Operational Semantics Using the Partiality
-- Monad" by Danielsson, implemented using both the quotient
-- inductive-inductive partiality monad, and the delay monad.
--
-- These developments to a large extent mirror developments in
-- "Coinductive big-step operational semantics" by Leroy and Grall.

-- The syntax of, and a type system for, the untyped λ-calculus with
-- constants.

import Lambda.Syntax

-- Most of a virtual machine.

import Lambda.Virtual-machine

-- A compiler.

import Lambda.Compiler

-- A definitional interpreter.

import Lambda.Partiality-monad.Inductive.Interpreter
import Lambda.Delay-monad.Interpreter

-- A type soundness result.

import Lambda.Partiality-monad.Inductive.Type-soundness
import Lambda.Delay-monad.Type-soundness

-- A virtual machine.

import Lambda.Partiality-monad.Inductive.Virtual-machine
import Lambda.Delay-monad.Virtual-machine

-- Compiler correctness.

import Lambda.Partiality-monad.Inductive.Compiler-correctness
import Lambda.Delay-monad.Compiler-correctness

------------------------------------------------------------------------
-- An untyped λ-calculus without constants

-- A variant of the development above. The development above uses a
-- well-scoped variant of the untyped λ-calculus with constants. This
-- development does not use constants. This means that the interpreter
-- cannot crash, so the type soundness result has been omitted.

import Lambda.Simplified.Syntax
import Lambda.Simplified.Virtual-machine
import Lambda.Simplified.Compiler
import Lambda.Simplified.Partiality-monad.Inductive.Interpreter
import Lambda.Simplified.Delay-monad.Interpreter
import Lambda.Simplified.Partiality-monad.Inductive.Virtual-machine
import Lambda.Simplified.Delay-monad.Virtual-machine
import Lambda.Simplified.Partiality-monad.Inductive.Compiler-correctness
import Lambda.Simplified.Delay-monad.Compiler-correctness
