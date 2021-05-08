------------------------------------------------------------------------
-- The delay monad quotiented by weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --cubical --sized-types #-}

module Partiality-monad.Coinductive where

open import Equality.Propositional.Cubical
open import Prelude hiding (⊥)
open import Prelude.Size

open import Bijection equality-with-J using (_↔_)
open import H-level equality-with-J
open import H-level.Truncation.Propositional equality-with-paths
open import Quotient equality-with-paths

open import Delay-monad
open import Delay-monad.Bisimilarity

-- The partiality monad, defined as the delay monad quotiented by
-- (propositionally truncated) weak bisimilarity.

_⊥ : ∀ {a} → Type a → Type a
A ⊥ = Delay A ∞ / λ x y → ∥ x ≈ y ∥

-- The partiality monad is a set.

⊥-is-set : ∀ {a} {A : Type a} → Is-set (A ⊥)
⊥-is-set = /-is-set
