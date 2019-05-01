------------------------------------------------------------------------
-- A function that runs computations
------------------------------------------------------------------------

{-# OPTIONS --cubical #-}

module Partiality-monad.Inductive.Approximate {a} {A : Set a} where

open import Equality.Propositional
open import Prelude hiding (⊥)

open import H-level.Truncation.Propositional equality-with-J

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Eliminators

-- Runs the computation. The given number is used to decide which
-- element to choose in sequences that are encountered.

approximate : A ⊥ → ℕ → ∥ Maybe A ∥
approximate x n = ⊥-rec-⊥
  (record
     { pe = ∣ nothing ∣
     ; po = λ x → ∣ just x ∣
     ; pl = λ _ rec → rec n
     ; pp = λ _ → truncation-is-proposition
     })
  x
