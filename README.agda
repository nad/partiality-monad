------------------------------------------------------------------------
-- Code related to the paper "Partiality, Revisited: The Partiality
-- Monad as a Quotient Inductive-Inductive Type"
--
-- Thorsten Altenkirch, Nils Anders Danielsson and Nicolai Kraus
------------------------------------------------------------------------

-- Comments of the form (§n) indicate that (parts of) the given
-- module(s) correspond to (parts of) Section n in the paper.

{-# OPTIONS --without-K #-}

module README where

------------------------------------------------------------------------
-- The partiality monad

-- The code is heavily inspired by the section on Cauchy reals in the
-- HoTT book (first edition).

-- A partial inductive-recursive definition of the partiality monad,
-- without path or truncation constructors, in order to get the basics
-- right.

import Partiality-monad.Inductive.Preliminary-sketch

-- Partiality algebras (§3.1).

import Partiality-monad.Inductive.Partiality-algebra

-- Partiality algebra properties that do not depend on initiality.

import Partiality-monad.Inductive.Partiality-algebra.Properties

-- A higher inductive-inductive definition of the partiality monad
-- (§3.1).

import Partiality-monad.Inductive

-- Specialised eliminators (§3.1).

import Partiality-monad.Inductive.Eliminators

-- A function that runs computations.

import Partiality-monad.Inductive.Approximate

-- An alternative characterisation of the information ordering, along
-- with related results (§3.3).

import Partiality-monad.Inductive.Alternative-order

-- Monotone functions (§5.1).

import Partiality-monad.Inductive.Monotone

-- ω-continuous functions (§5.1).

import Partiality-monad.Inductive.Omega-continuous

-- The partiality monad's monad instance (§3.2).

import Partiality-monad.Inductive.Monad

-- Strict ω-continuous functions.

import Partiality-monad.Inductive.Strict-omega-continuous

-- Fixpoint combinators (§5.1).

import Partiality-monad.Inductive.Fixpoints

------------------------------------------------------------------------
-- The delay monad (§4)

-- The delay monad, defined coinductively.

import Delay-monad

-- Strong bisimilarity.

import Delay-monad.Strong-bisimilarity

-- Weak bisimilarity.

import Delay-monad.Weak-bisimilarity

-- An alternative definition of the delay monad (§4.1).

import Delay-monad.Alternative

-- A partial order.

import Delay-monad.Partial-order

-- Least upper bounds.

import Delay-monad.Least-upper-bound

-- The delay monad is a monad up to strong bisimilarity.

import Delay-monad.Monad

-- The "always true" predicate, □.

import Delay-monad.Always

------------------------------------------------------------------------
-- An example (§5.3)

-- Some developments from "Operational Semantics Using the Partiality
-- Monad" by Danielsson, implemented using both the higher
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
-- A simplified example

-- A simplified variant of the example above. The example above uses a
-- well-scoped variant of the untyped λ-calculus with constants. This
-- example does not use constants. This means that the interpreter
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

------------------------------------------------------------------------
-- A variant of the delay monad with a sized type parameter

-- The delay monad, defined coinductively, with a sized type
-- parameter.

import Delay-monad.Sized

-- Strong bisimilarity.

import Delay-monad.Sized.Strong-bisimilarity

-- Weak bisimilarity.

import Delay-monad.Sized.Weak-bisimilarity

-- A partial order.

import Delay-monad.Sized.Partial-order

-- Least upper bounds.

import Delay-monad.Sized.Least-upper-bound

-- A monad-like structure.

import Delay-monad.Sized.Monad

-- The "always true" predicate, □.

import Delay-monad.Sized.Always

------------------------------------------------------------------------
-- The delay monad quotiented by weak bisimilarity

-- The delay monad quotiented by weak bisimilarity (§4).

import Partiality-monad.Coinductive

-- A partial order.

import Partiality-monad.Coinductive.Partial-order

-- An alternative definition of the partiality monad: a variant of the
-- delay monad quotiented by a notion of weak bisimilarity.

import Partiality-monad.Coinductive.Alternative

------------------------------------------------------------------------
-- A proof of equivalence (§4.2)

-- The partiality monads in Partiality-monad.Inductive and
-- Partiality-monad.Coinductive are pointwise equivalent, for sets,
-- assuming extensionality, propositional extensionality and countable
-- choice.

import Partiality-monad.Equivalence

------------------------------------------------------------------------
-- ω-CPOs

-- Pointed and non-pointed ω-CPOs.

import Omega-CPO

-- The code in the following three modules is based on a suggestion
-- from Paolo Capriotti.

-- A partial inductive-recursive definition of the lifting
-- construction on ω-CPOs, without path or truncation constructors, in
-- order to get the basics right.

import Lifting.Preliminary-sketch

-- A higher inductive-inductive definition of the lifting construction
-- on ω-CPOs.

import Lifting

-- An alternative but equivalent definition of the partiality monad,
-- based on the lifting construction in Lifting.

import Lifting.Partiality-monad
