------------------------------------------------------------------------
-- Code related to the paper "Partiality, Revisited: The Partiality
-- Monad as a Quotient Inductive-Inductive Type"
--
-- Thorsten Altenkirch, Nils Anders Danielsson and Nicolai Kraus
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README where

-- Note that our definition of the partiality monad and some of the
-- results are heavily inspired by the section on Cauchy reals in the
-- HoTT book (first edition).

-- The partiality algebra code uses ideas and concepts from "Inductive
-- types in homotopy type theory" by Awodey, Gambino and Sojakova,
-- "Inductive Types in Homotopy Type Theory" by Sojakova, "Quotient
-- inductive-inductive types" by Altenkirch, Capriotti, Dijkstra and
-- Nordvall Forsberg, and Gabe Dijkstra's forthcoming PhD thesis.

------------------------------------------------------------------------
-- Pointers to results from the paper

-- In order to more easily find code corresponding to results from the
-- paper, see the following module. Note that some of the code
-- referenced below is not discussed at all in the paper.

import README.Pointers-to-results-from-the-paper

------------------------------------------------------------------------
-- Preliminaries

-- A partial inductive-recursive definition of the partiality monad,
-- without path or truncation constructors, in order to get the basics
-- right.

import Partiality-monad.Inductive.Preliminary-sketch

------------------------------------------------------------------------
-- Partiality algebras

-- Partiality algebras.

import Partiality-algebra

-- Some partiality algebra properties.

import Partiality-algebra.Properties

-- Partiality algebra categories.

import Partiality-algebra.Category

-- Eliminators and initiality.

import Partiality-algebra.Eliminators

-- Monotone functions.

import Partiality-algebra.Monotone

-- ω-continuous functions.

import Partiality-algebra.Omega-continuous

-- Strict ω-continuous functions.

import Partiality-algebra.Strict-omega-continuous

-- Fixpoint combinators.

import Partiality-algebra.Fixpoints

-- Pi with partiality algebra families as codomains.

import Partiality-algebra.Pi

------------------------------------------------------------------------
-- The partiality monad

-- A quotient inductive-inductive definition of the partiality monad.

import Partiality-monad.Inductive

-- Specialised eliminators.

import Partiality-monad.Inductive.Eliminators

-- A function that runs computations.

import Partiality-monad.Inductive.Approximate

-- An alternative characterisation of the information ordering, along
-- with related results.

import Partiality-monad.Inductive.Alternative-order

-- Monotone functions.

import Partiality-monad.Inductive.Monotone

-- ω-continuous functions.

import Partiality-monad.Inductive.Omega-continuous

-- The partiality monad's monad instance.

import Partiality-monad.Inductive.Monad

-- The partiality monad's monad instance, defined via an adjunction.

import Partiality-monad.Inductive.Monad.Adjunction

-- Strict ω-continuous functions.

import Partiality-monad.Inductive.Strict-omega-continuous

-- Fixpoint combinators.

import Partiality-monad.Inductive.Fixpoints

------------------------------------------------------------------------
-- Some examples

-- A function that, given a stream, tries to find an element
-- satisfying a predicate.

import Search

-- Examples involving simple λ-calculi.

import README.Lambda

------------------------------------------------------------------------
-- An alternative definition of the delay monad

-- The delay monad, defined using increasing sequences of potential
-- values.

import Delay-monad.Alternative

-- Various properties.

import Delay-monad.Alternative.Properties

-- Theorems relating the coinductive definition of the delay
-- monad to the alternative one and to another type.

import Delay-monad.Alternative.Equivalence

-- Termination predicates.

import Delay-monad.Alternative.Termination

-- Information orderings.

import Delay-monad.Alternative.Partial-order

-- Weak bisimilarity.

import Delay-monad.Alternative.Weak-bisimilarity

-- Two eliminators for Delay-monad.Alternative.Delay (A / R).

import Delay-monad.Alternative.Eliminators

------------------------------------------------------------------------
-- The delay monad quotiented by weak bisimilarity

-- The delay monad quotiented by weak bisimilarity.

import Partiality-monad.Coinductive

-- A partial order.

import Partiality-monad.Coinductive.Partial-order

-- An alternative definition of the partiality monad: a variant of the
-- delay monad quotiented by a notion of weak bisimilarity.

import Partiality-monad.Coinductive.Alternative

------------------------------------------------------------------------
-- A proof of equivalence

-- The partiality monads in Partiality-monad.Inductive and
-- Partiality-monad.Coinductive are pointwise equivalent, for sets,
-- assuming extensionality, propositional extensionality and countable
-- choice.

import Partiality-monad.Equivalence

------------------------------------------------------------------------
-- ω-cpos

-- Pointed and non-pointed ω-cpos.

import Omega-cpo

-- The code in the following three modules is based on a suggestion
-- from Paolo Capriotti.

-- A partial inductive-recursive definition of the lifting
-- construction on ω-cpos, without path or truncation constructors, in
-- order to get the basics right.

import Lifting.Preliminary-sketch

-- A quotient inductive-inductive definition of the lifting
-- construction on ω-cpos.

import Lifting

-- An alternative but equivalent definition of the partiality monad
-- (but only for sets), based on the lifting construction in Lifting.

import Lifting.Partiality-monad
