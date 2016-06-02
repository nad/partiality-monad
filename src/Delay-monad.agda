------------------------------------------------------------------------
-- The delay monad, defined coinductively
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad where

open import Prelude

-- The delay monad.

mutual

  Delay : ∀ {a} → Set a → Size → Set a
  Delay A i = A ⊎ ∞Delay A i

  record ∞Delay {a} (A : Set a) (i : Size) : Set a where
    coinductive
    field
      force : {j : Size< i} → Delay A j

open ∞Delay public

pattern now x   = inj₁ x
pattern later x = inj₂ x

module _ {a} {A : Set a} where

  mutual

    -- A non-terminating computation.

    never : Delay A ∞
    never = later ∞never

    ∞never : ∞Delay A ∞
    force ∞never = never
