------------------------------------------------------------------------
-- Code related to the paper "Partiality, Revisited"
-- Thorsten Altenkirch and Nils Anders Danielsson
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README where

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
