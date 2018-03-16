------------------------------------------------------------------------
-- The delay monad quotiented by weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Partiality-monad.Coinductive where

open import Equality.Propositional
open import H-level.Truncation.Propositional
open import Prelude hiding (⊥)
open import Quotient.HIT

open import H-level equality-with-J

open import Delay-monad
open import Delay-monad.Bisimilarity

-- The partiality monad, defined as the delay monad quotiented by
-- (propositionally truncated) weak bisimilarity.

_⊥ : ∀ {a} → Set a → Set a
A ⊥ = Delay A ∞ / λ x y → ∥ x ≈ y ∥ , truncation-is-proposition

-- The partiality monad is a set.

⊥-is-set : ∀ {a} {A : Set a} → Is-set (A ⊥)
⊥-is-set = /-is-set
