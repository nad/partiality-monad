------------------------------------------------------------------------
-- A function that runs computations
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

open import Prelude hiding (⊥)

module Partiality-monad.Inductive.Approximate {a} {A : Type a} where

open import Equality.Propositional.Cubical

open import H-level.Truncation.Propositional equality-with-paths

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
