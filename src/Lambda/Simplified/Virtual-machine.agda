------------------------------------------------------------------------
-- Most of a virtual machine
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Lambda.Simplified.Virtual-machine where

open import Prelude

open import Lambda.Simplified.Syntax

------------------------------------------------------------------------
-- Instruction set

mutual

  -- Instructions.

  data Instr (n : ℕ) : Set where
    var : (x : Fin n) → Instr n
    clo : (c : Code (suc n)) → Instr n
    app : Instr n
    ret : Instr n

  -- Code.

  Code : ℕ → Set
  Code n = List (Instr n)

-- Environments and values.

open Closure Code

------------------------------------------------------------------------
-- Stacks and states

-- Stacks.

data StackElement : Set where
  val : (v : Value) → StackElement
  ret : ∀ {n} (c : Code n) (ρ : Env n) → StackElement

Stack : Set
Stack = List StackElement

-- States.

data State : Set where
  ⟨_,_,_⟩ : ∀ {n} (c : Code n) (s : Stack) (ρ : Env n) → State

pattern ⟨_∣_,_,_⟩ n c s ρ = ⟨_,_,_⟩ {n} c s ρ

------------------------------------------------------------------------
-- A kind of small-step semantics for the virtual machine

-- The result of running the VM one step.

data Result : Set where
  continue : (s : State) → Result
  done     : (v : Value) → Result
  crash    : Result

-- A single step of the computation.

step : State → Result
step ⟨ var x  ∷ c ,                          s , ρ ⟩ = continue ⟨ c  , val (ρ x)    ∷ s ,      ρ    ⟩
step ⟨ clo c′ ∷ c ,                          s , ρ ⟩ = continue ⟨ c  , val (ƛ c′ ρ) ∷ s ,      ρ    ⟩
step ⟨ app    ∷ c , val v ∷ val (ƛ c′ ρ′) ∷  s , ρ ⟩ = continue ⟨ c′ , ret c ρ      ∷ s , snoc ρ′ v ⟩
step ⟨ ret    ∷ c , val v ∷ ret c′ ρ′     ∷  s , ρ ⟩ = continue ⟨ c′ , val v        ∷ s ,      ρ′   ⟩
step ⟨ zero ∣ []  ,                 val v ∷ [] , ρ ⟩ = done v
step _                                               = crash
