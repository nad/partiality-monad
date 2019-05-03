------------------------------------------------------------------------
-- A virtual machine
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe --sized-types #-}

module Lambda.Partiality-monad.Inductive.Virtual-machine where

open import Prelude hiding (⊥)

open import Partiality-monad.Inductive

open import Lambda.Syntax
open import Lambda.Virtual-machine

open Closure Code

-- A functional semantics for the VM.
--
-- For an alternative definition, see the semantics in
-- Lambda.Simplified.Partiality-monad.Inductive.Virtual-machine, which
-- is defined using a fixpoint combinator.

steps : State → ℕ → Maybe Value ⊥
steps s n       with step s
steps s zero    | continue s′ = never
steps s (suc n) | continue s′ = steps s′ n
steps s n       | done v      = now (just v)
steps s n       | crash       = now nothing

steps-increasing : ∀ s n → steps s n ⊑ steps s (suc n)
steps-increasing s n       with step s
steps-increasing s zero    | continue s′ = never⊑ _
steps-increasing s (suc n) | continue s′ = steps-increasing s′ n
steps-increasing s n       | done v      = ⊑-refl _
steps-increasing s n       | crash       = ⊑-refl _

stepsˢ : State → Increasing-sequence (Maybe Value)
stepsˢ s = (steps s , steps-increasing s)

exec : State → Maybe Value ⊥
exec s = ⨆ (stepsˢ s)
