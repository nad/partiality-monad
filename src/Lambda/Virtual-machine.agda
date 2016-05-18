------------------------------------------------------------------------
-- A virtual machine
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Lambda.Virtual-machine where

open import Prelude hiding (⊥)

open import Partiality-monad.Inductive

open import Lambda.Syntax

------------------------------------------------------------------------
-- Instruction set

mutual

  -- Instructions.

  data Instr (n : ℕ) : Set where
    var : (x : Fin n) → Instr n
    con : (i : ℕ) → Instr n
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
-- Functional semantics of the VM

-- The result of running the VM one step.

data Result : Set where
  continue : (s : State) → Result
  done     : (v : Value) → Result
  crash    : Result

-- A single step of the computation.

step : State → Result
step ⟨ var x  ∷ c ,                          s , ρ ⟩ = continue ⟨ c  , val (ρ x)    ∷ s ,      ρ    ⟩
step ⟨ con i  ∷ c ,                          s , ρ ⟩ = continue ⟨ c  , val (con i)  ∷ s ,      ρ    ⟩
step ⟨ clo c′ ∷ c ,                          s , ρ ⟩ = continue ⟨ c  , val (ƛ c′ ρ) ∷ s ,      ρ    ⟩
step ⟨ app    ∷ c , val v ∷ val (ƛ c′ ρ′) ∷  s , ρ ⟩ = continue ⟨ c′ , ret c ρ      ∷ s , snoc ρ′ v ⟩
step ⟨ ret    ∷ c , val v ∷ ret c′ ρ′     ∷  s , ρ ⟩ = continue ⟨ c′ , val v        ∷ s ,      ρ′   ⟩
step ⟨ zero ∣ []  ,                 val v ∷ [] , ρ ⟩ = done v
step _                                               = crash

-- The VM.

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
