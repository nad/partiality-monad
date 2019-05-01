------------------------------------------------------------------------
-- The delay monad quotiented by weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --cubical #-}

module Partiality-monad.Coinductive where

open import Equality.Propositional
open import Prelude hiding (⊥)
open import Size

open import Bijection equality-with-J using (_↔_)
open import H-level equality-with-J
open import H-level.Truncation.Propositional equality-with-J
open import Quotient.HIT equality-with-J

open import Delay-monad
open import Delay-monad.Bisimilarity

-- The partiality monad, defined as the delay monad quotiented by
-- (propositionally truncated) weak bisimilarity.

_⊥ : ∀ {a} → Set a → Set a
A ⊥ = Delay A ∞ / λ x y → ∥ x ≈ y ∥

-- The partiality monad is a set.

⊥-is-set : ∀ {a} {A : Set a} → Is-set (A ⊥)
⊥-is-set = /-is-set
