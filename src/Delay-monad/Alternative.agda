------------------------------------------------------------------------
-- The delay monad, defined using increasing sequences of potential
-- values
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Delay-monad.Alternative where

open import Equality.Propositional
open import Prelude hiding (↑)

------------------------------------------------------------------------
-- _↓_ and _↑

module _ {a} {A : Set a} where

  infix 4 _↑ _↓_

  -- x ↓ y means that the computation x has the value y.

  _↓_ : Maybe A → A → Set a
  x ↓ y = x ≡ just y

  -- x ↑ means that the computation x does not have a value.

  _↑ : Maybe A → Set a
  x ↑ = x ≡ nothing

------------------------------------------------------------------------
-- An alternative definition of the delay monad

module _ {a} {A : Set a} where

  -- The property of being an increasing sequence.

  LE : Maybe A → Maybe A → Set a
  LE x y = x ≡ y ⊎ (x ↑ × ¬ y ↑)

  Increasing-at : ℕ → (ℕ → Maybe A) → Set a
  Increasing-at n f = LE (f n) (f (suc n))

  Increasing : (ℕ → Maybe A) → Set a
  Increasing f = ∀ n → Increasing-at n f

-- An alternative definition of the delay monad.

Delay : ∀ {a} → Set a → Set a
Delay A = ∃ λ (f : ℕ → Maybe A) → Increasing f
