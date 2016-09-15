------------------------------------------------------------------------
-- A virtual machine
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Lambda.Simplified.Partiality-monad.Inductive.Virtual-machine
  where

open import Equality.Propositional
open import Prelude hiding (⊥)

open import Monad equality-with-J

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Fixpoints

open import Lambda.Simplified.Syntax
open import Lambda.Simplified.Virtual-machine

open Closure Code

-- A functional semantics for the VM.

execP : State → Partial State (λ _ → Maybe Value) (Maybe Value)
execP s with step s
... | continue s′ = rec s′
... | done v      = return (just v)
... | crash       = return nothing

exec : State → Maybe Value ⊥
exec s = fixP execP s
