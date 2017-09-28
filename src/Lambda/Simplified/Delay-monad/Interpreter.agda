------------------------------------------------------------------------
-- A definitional interpreter
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Lambda.Simplified.Delay-monad.Interpreter where

open import Equality.Propositional
open import Prelude

open import Monad equality-with-J

open import Delay-monad
open import Delay-monad.Monad
open import Delay-monad.Strong-bisimilarity
open import Delay-monad.Weak-bisimilarity

open import Lambda.Simplified.Syntax

open Closure Tm

------------------------------------------------------------------------
-- The interpreter

infix 10 _∙_

mutual

  ⟦_⟧ : ∀ {i n} → Tm n → Env n → Delay Value i
  ⟦ var x ⟧   ρ = return (ρ x)
  ⟦ ƛ t ⟧     ρ = return (ƛ t ρ)
  ⟦ t₁ · t₂ ⟧ ρ = ⟦ t₁ ⟧ ρ >>= λ v₁ →
                  ⟦ t₂ ⟧ ρ >>= λ v₂ →
                  v₁ ∙ v₂

  _∙_ : ∀ {i} → Value → Value → Delay Value i
  ƛ t₁ ρ ∙ v₂ = later λ { .force → ⟦ t₁ ⟧ (snoc ρ v₂) }

------------------------------------------------------------------------
-- An example

-- The semantics of Ω is the non-terminating computation never.

Ω-loops : ⟦ Ω ⟧ empty ∼ never
Ω-loops = later λ { .force → Ω-loops }
