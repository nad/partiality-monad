------------------------------------------------------------------------
-- A virtual machine
------------------------------------------------------------------------

{-# OPTIONS --safe --sized-types #-}

module Lambda.Delay-monad.Virtual-machine where

open import Equality.Propositional

open import Maybe equality-with-J
open import Monad equality-with-J

open import Delay-monad
open import Delay-monad.Monad

open import Lambda.Delay-monad.Interpreter
open import Lambda.Syntax
open import Lambda.Virtual-machine

open Closure Code

mutual

  -- A functional semantics for the VM.

  exec : ∀ {i} → State → M i Value
  exec s with step s
  ... | continue s′ = laterM (∞exec s′)
  ... | done v      = return v
  ... | crash       = fail

  ∞exec : ∀ {i} → State → M′ i Value
  force (run (∞exec s)) = run (exec s)
