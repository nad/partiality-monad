------------------------------------------------------------------------
-- Strong bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad.Sized.Strong-bisimilarity where

open import Equality.Propositional using (_≡_)
open import Prelude

open import Delay-monad.Sized

module _ {a} {A : Size → Set a} where

  -- Strong bisimilarity. Note that this type is not defined in the
  -- same way as Delay. One might argue that the now-cong constructor
  -- should have the following type, using a /sized/ identity type Id:
  --
  --   now-cong : ∀ {x y} →
  --              Id (A ∞) i x y →
  --              Strongly-bisimilar i (now x) (now y)

  mutual

    data Strongly-bisimilar
           (i : Size) : (x y : Delay A ∞) → Set a where
      now-cong   : ∀ {x} → Strongly-bisimilar i (now x) (now x)
      later-cong : ∀ {x y} →
                   ∞Strongly-bisimilar i (force x) (force y) →
                   Strongly-bisimilar i (later x) (later y)

    record ∞Strongly-bisimilar
             (i : Size) (x y : Delay A ∞) : Set a where
      coinductive
      field
        force : {j : Size< i} → Strongly-bisimilar j x y

  open ∞Strongly-bisimilar public

  infix 4 _∼_ _∞∼_

  _∼_ : Delay A ∞ → Delay A ∞ → Set a
  _∼_ = Strongly-bisimilar ∞

  _∞∼_ : Delay A ∞ → Delay A ∞ → Set a
  _∞∼_ = ∞Strongly-bisimilar ∞

-- A statement of extensionality: strongly bisimilar computations are
-- equal.

Extensionality : (ℓ : Level) → Set (lsuc ℓ)
Extensionality a =
  {A : Size → Set a} {x y : Delay A ∞} → x ∼ y → x ≡ y

module _ {a} {A : Size → Set a} where

  mutual

    -- Strong bisimilarity is reflexive.

    reflexive : (x : Delay A ∞) → x ∼ x
    reflexive (now x)   = now-cong
    reflexive (later x) = later-cong (∞reflexive (force x))

    ∞reflexive : (x : Delay A ∞) → x ∞∼ x
    force (∞reflexive x) = reflexive x

  mutual

    -- Strong bisimilarity is symmetric.

    symmetric : ∀ {i} {x y : Delay A ∞} →
                Strongly-bisimilar i x y →
                Strongly-bisimilar i y x
    symmetric now-cong       = now-cong
    symmetric (later-cong p) = later-cong (∞symmetric p)

    ∞symmetric : ∀ {i} {x y : Delay A ∞} →
                 ∞Strongly-bisimilar i x y →
                 ∞Strongly-bisimilar i y x
    force (∞symmetric p) = symmetric (force p)

  mutual

    -- Strong bisimilarity is transitive.

    transitive : ∀ {i} {x y z : Delay A ∞} →
                 Strongly-bisimilar i x y →
                 Strongly-bisimilar i y z →
                 Strongly-bisimilar i x z
    transitive now-cong       now-cong       = now-cong
    transitive (later-cong p) (later-cong q) =
      later-cong (∞transitive p q)

    ∞transitive : ∀ {i} {x y z : Delay A ∞} →
                  ∞Strongly-bisimilar i x y →
                  ∞Strongly-bisimilar i y z →
                  ∞Strongly-bisimilar i x z
    force (∞transitive p q) = transitive (force p) (force q)
