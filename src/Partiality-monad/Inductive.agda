------------------------------------------------------------------------
-- A quotient inductive-inductive definition of the partiality monad
------------------------------------------------------------------------

-- Note that this module is experimental: it uses postulates to encode
-- a quotient inductive-inductive type.

{-# OPTIONS --cubical #-}

module Partiality-monad.Inductive where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms equality-with-J using (ext)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J hiding (Type)
open import H-level.Closure equality-with-J

open import Partiality-algebra as PA
open import Partiality-algebra.Eliminators as PAE hiding (Arguments)
import Partiality-algebra.Properties

-- The partiality monad's type formers and constructors.

postulate
  partiality-algebra : ∀ {a} (A : Set a) → Partiality-algebra a a A

module _ {a} {A : Set a} where

  open Partiality-algebra (partiality-algebra A) public
    hiding (Type; Increasing-sequence)
    renaming ( Type-is-set to ⊥-is-set
             ; equality-characterisation-Type to
               equality-characterisation-⊥
             )

  open Partiality-algebra.Properties (partiality-algebra A) public

-- The partiality monad.

infix 10 _⊥

_⊥ : ∀ {a} → Set a → Set a
A ⊥ = Partiality-algebra.Type (partiality-algebra A)

-- Increasing sequences.

Increasing-sequence : ∀ {a} → Set a → Set a
Increasing-sequence A =
  Partiality-algebra.Increasing-sequence (partiality-algebra A)

module _ {a p q} {A : Set a} where

  -- The elimination principle.

  postulate
    eliminators : Elimination-principle p q (partiality-algebra A)

  module _ args where
    open Eliminators (eliminators args) public

  -- Initiality.

  initial : Initial p q (partiality-algebra A)
  initial = eliminators→initiality _ eliminators

-- The eliminators' arguments.

Arguments : ∀ {a} p q (A : Set a) → Set (a ⊔ lsuc (p ⊔ q))
Arguments p q A = PAE.Arguments p q (partiality-algebra A)
