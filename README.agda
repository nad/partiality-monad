------------------------------------------------------------------------
-- Code related to the paper "Partiality, Revisited"
-- Thorsten Altenkirch, Nils Anders Danielsson and Nicolai Kraus
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README where

------------------------------------------------------------------------
-- The partiality monad

-- The code is heavily inspired by the section on Cauchy reals in the
-- HoTT book (first edition).

-- A partial inductive definition of the partiality monad, without
-- path or truncation constructors, in order to get the basics right.

import Partiality-monad.Inductive.Preliminary-sketch

-- A higher inductive-inductive definition of the partiality monad.

import Partiality-monad.Inductive

-- Specialised eliminators.

import Partiality-monad.Inductive.Eliminators

-- Some definitions and properties.

import Partiality-monad.Inductive.Properties

-- An alternative characterisation of the information ordering, along
-- with related results.

import Partiality-monad.Inductive.Alternative-order

-- Monotone functions.

import Partiality-monad.Inductive.Monotone

-- ω-continuous functions.

import Partiality-monad.Inductive.Omega-continuous

-- The partiality monad's monad instance.

import Partiality-monad.Inductive.Monad

-- Strict ω-continuous functions.

import Partiality-monad.Inductive.Strict-omega-continuous

-- Fixpoint combinators.

import Partiality-monad.Inductive.Fixpoints

------------------------------------------------------------------------
-- The delay monad

-- The delay monad, defined coinductively.

import Delay-monad

-- Strong bisimilarity.

import Delay-monad.Strong-bisimilarity

-- Weak bisimilarity.

import Delay-monad.Weak-bisimilarity

-- An alternative definition of the delay monad.

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
-- An example

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

-- The delay monad quotiented by weak bisimilarity.

import Partiality-monad.Coinductive

-- A partial order.

import Partiality-monad.Coinductive.Partial-order

------------------------------------------------------------------------
-- A proof of equivalence

-- The partiality monads in Partiality-monad.Inductive and
-- Partiality-monad.Coinductive are pointwise equivalent, for sets,
-- assuming extensionality, univalence and countable choice.

import Countchoice-equiv
import Partiality-monad.Equivalence
