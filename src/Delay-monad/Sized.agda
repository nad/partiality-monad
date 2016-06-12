------------------------------------------------------------------------
-- The delay monad, defined coinductively, with a sized type parameter
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad.Sized where

open import Prelude

-- The delay monad.

mutual

  Delay : ∀ {a} → (Size → Set a) → Size → Set a
  Delay A i = A i ⊎ ∞Delay A i

  record ∞Delay {a} (A : Size → Set a) (i : Size) : Set a where
    coinductive
    field
      force : {j : Size< i} → Delay A j

open ∞Delay public

pattern now x   = inj₁ x
pattern later x = inj₂ x

module _ {a} {A : Size → Set a} where

  mutual

    -- A non-terminating computation.

    never : ∀ {i} → Delay A i
    never = later ∞never

    ∞never : ∀ {i} → ∞Delay A i
    force ∞never = never
