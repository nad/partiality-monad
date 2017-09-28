------------------------------------------------------------------------
-- A virtual machine
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Lambda.Simplified.Delay-monad.Virtual-machine where

open import Equality.Propositional
open import Prelude

open import Monad equality-with-J

open import Delay-monad
open import Delay-monad.Monad

open import Lambda.Simplified.Delay-monad.Interpreter
open import Lambda.Simplified.Syntax
open import Lambda.Simplified.Virtual-machine

open Closure Code

-- A functional semantics for the VM.

exec : ∀ {i} → State → Delay (Maybe Value) i
exec s with step s
... | continue s′ = later λ { .force → exec s′ }
... | done v      = return (just v)
... | crash       = return nothing
