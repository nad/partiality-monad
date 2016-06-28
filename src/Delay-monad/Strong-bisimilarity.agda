------------------------------------------------------------------------
-- Strong bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad.Strong-bisimilarity where

open import Equality.Propositional using (_≡_; subst; sym)
open import Prelude

open import Delay-monad

module _ {a} {A : Set a} where

  -- Strong bisimilarity.

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
  {A : Set a} {x y : Delay A ∞} → x ∼ y → x ≡ y

module _ {a} {A : Set a} where

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

  -- Some equational reasoning combinators.

  infix  -1 finally-∼ _∎∼
  infixr -2 _∼⟨_⟩_ _∼⟨⟩_ _≡⟨_⟩∼_

  _∎∼ : ∀ {i} (x : Delay A ∞) → Strongly-bisimilar i x x
  _∎∼ = reflexive

  _∼⟨_⟩_ : ∀ {i} (x : Delay A ∞) {y z} →
           Strongly-bisimilar i x y → Strongly-bisimilar i y z →
           Strongly-bisimilar i x z
  _ ∼⟨ p ⟩ q = transitive p q

  _∼⟨⟩_ : ∀ {i} (x : Delay A ∞) {y} →
          Strongly-bisimilar i x y → Strongly-bisimilar i x y
  _ ∼⟨⟩ p = p

  _≡⟨_⟩∼_ : ∀ {i} (x : Delay A ∞) {y z} →
            x ≡ y → Strongly-bisimilar i y z → Strongly-bisimilar i x z
  _≡⟨_⟩∼_ {i} _ p q = subst (λ x → Strongly-bisimilar i x _) (sym p) q

  finally-∼ : ∀ {i} (x y : Delay A ∞) →
              Strongly-bisimilar i x y → Strongly-bisimilar i x y
  finally-∼ _ _ p = p

  syntax finally-∼ x y p = x ∼⟨ p ⟩∎ y ∎
