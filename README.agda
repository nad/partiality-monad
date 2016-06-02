------------------------------------------------------------------------
-- Code related to the paper "Partiality, Revisited"
-- Thorsten Altenkirch and Nils Anders Danielsson
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
-- An example

-- Some developments from "Operational Semantics Using the Partiality
-- Monad" by Danielsson, implemented using the higher
-- inductive-inductive partiality monad.
--
-- These developments to a large extent mirror developments in
-- "Coinductive big-step operational semantics" by Leroy and Grall.

-- The syntax of, and a type system for, the untyped λ-calculus with
-- constants.

import Lambda.Syntax

-- A definitional interpreter.

import Lambda.Interpreter

-- A type soundness result.

import Lambda.Type-soundness

-- A virtual machine.

import Lambda.Virtual-machine

-- A correct compiler.

import Lambda.Compiler

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

------------------------------------------------------------------------
-- The delay monad quotiented by weak bisimilarity

-- The delay monad quotiented by weak bisimilarity.

import Partiality-monad.Coinductive

-- A partial order.

import Partiality-monad.Coinductive.Partial-order
