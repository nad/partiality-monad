------------------------------------------------------------------------
-- A compiler
------------------------------------------------------------------------

{-# OPTIONS --cubical #-}

module Lambda.Compiler where

open import Equality.Propositional
open import Prelude

open import Equality.Path.Isomorphisms equality-with-J using (⟨ext⟩)

open import Lambda.Syntax hiding ([_])
open import Lambda.Virtual-machine

private
  module C = Closure Code
  module T = Closure Tm

-- The compiler (which takes a code continuation).

comp : ∀ {n} → Tm n → Code n → Code n
comp (con i)   c = con i ∷ c
comp (var x)   c = var x ∷ c
comp (ƛ t)     c = clo (comp t (ret ∷ [])) ∷ c
comp (t₁ · t₂) c = comp t₁ (comp t₂ (app ∷ c))

-- Environments and values can also be compiled.

mutual

  comp-env : ∀ {n} → T.Env n → C.Env n
  comp-env ρ n = comp-val (ρ n)

  comp-val : T.Value → C.Value
  comp-val (T.con i) = C.con i
  comp-val (T.ƛ t ρ) = C.ƛ (comp t (ret ∷ [])) (comp-env ρ)

-- Compilation takes empty environments to empty environments.

comp-empty : comp-env empty ≡ empty
comp-empty = ⟨ext⟩ (λ ())

-- Compilation commutes with snoc.

comp-snoc : ∀ {n} {ρ : T.Env n} {v} →
            comp-env (snoc ρ v) ≡ snoc (comp-env ρ) (comp-val v)
comp-snoc = ⟨ext⟩ [ (λ _ → refl) , (λ _ → refl) ]
