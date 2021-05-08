------------------------------------------------------------------------
-- The syntax of the untyped λ-calculus
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Lambda.Simplified.Syntax where

open import Equality.Propositional
open import Prelude

open import Vec.Function equality-with-J

------------------------------------------------------------------------
-- Terms

-- Variables are represented using de Bruijn indices.

infixl 9 _·_

data Tm (n : ℕ) : Type where
  var : (x : Fin n) → Tm n
  ƛ   : Tm (suc n) → Tm n
  _·_ : Tm n → Tm n → Tm n

------------------------------------------------------------------------
-- Closure-based definition of values

-- Environments and values. Defined in a module parametrised by the
-- type of terms.

module Closure (Tm : ℕ → Type) where

  mutual

    -- Environments.

    Env : ℕ → Type
    Env n = Vec Value n

    -- Values. Lambdas are represented using closures, so values do
    -- not contain any free variables.

    data Value : Type where
      ƛ : ∀ {n} (t : Tm (suc n)) (ρ : Env n) → Value

------------------------------------------------------------------------
-- Examples

-- A non-terminating term.

ω : Tm 0
ω = ƛ (var fzero · var fzero)

Ω : Tm 0
Ω = ω · ω

-- A call-by-value fixpoint combinator.

Z : Tm 0
Z = ƛ (t · t)
  where
  t = ƛ (var (fsuc fzero) ·
         ƛ (var (fsuc fzero) · var (fsuc fzero) · var fzero))
