------------------------------------------------------------------------
-- Least upper bounds
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad.Least-upper-bound where

open import Equality.Propositional hiding (reflexive)
open import Prelude hiding (_⊔_)

open import Nat equality-with-J

open import Delay-monad
open import Delay-monad.Partial-order

module _ {a} {A : Set a} where

  mutual

    -- Least upper bounds (if they exist).

    infix 10 _⊔_

    _⊔_ : ∀ {i} → Delay A i → Delay A i → Delay A i
    now x   ⊔ _       = now x
    later x ⊔ now y   = now y
    later x ⊔ later y = later (x ∞⊔ y)

    _∞⊔_ : ∀ {i} → ∞Delay A i → ∞Delay A i → ∞Delay A i
    force (x ∞⊔ y) = force x ⊔ force y

  mutual

    -- The computation x ⊔ y is smaller than or equal to every upper
    -- bound of x and y.

    ⊔-least-upper-bound : ∀ {i x y z} →
                          LE i x z → LE i y z → LE i (x ⊔ y) z
    ⊔-least-upper-bound               now-cong   _ = now-cong
    ⊔-least-upper-bound               (laterʳ p) q = laterʳ (⊔-least-upper-bound p (laterʳ⁻¹ q))
    ⊔-least-upper-bound {y = now y}   (laterˡ _) q = q
    ⊔-least-upper-bound {y = later y} (laterˡ p) q = laterˡ (∞⊔-least-upper-bound p (laterˡ⁻¹ q))

    ∞⊔-least-upper-bound : ∀ {i x y z} →
                           ∞LE i x z → ∞LE i y z → ∞LE i (x ⊔ y) z
    force (∞⊔-least-upper-bound p q) =
      ⊔-least-upper-bound (force p) (force q)

  mutual

    -- If x and y have a lower bound, then this is also a lower
    -- bound of x ⊔ y.

    ⊔-lower-bound : ∀ {i x y z} → LE i z x → LE i z y → LE i z (x ⊔ y)
    ⊔-lower-bound               now-cong   _ = now-cong
    ⊔-lower-bound               (laterˡ p) q = laterˡ (∞⊔-lower-bound p (laterˡ⁻¹ q))
    ⊔-lower-bound {y = now y}   (laterʳ _) q = q
    ⊔-lower-bound {y = later y} (laterʳ p) q = laterʳ (⊔-lower-bound p (laterʳ⁻¹ q))

    ∞⊔-lower-bound : ∀ {i x y z} → ∞LE i z x → ∞LE i z y → ∞LE i z (x ⊔ y)
    force (∞⊔-lower-bound p q) = ⊔-lower-bound (force p) (force q)

  mutual

    -- If x and y have an upper bound, then x ⊔ y is an upper bound
    -- of y.

    ⊔-upper-boundʳ : ∀ {i x y z} →
                     LE i x z → LE i y z → LE i y (x ⊔ y)
    ⊔-upper-boundʳ               now-cong   q = q
    ⊔-upper-boundʳ               (laterʳ p) q = ⊔-upper-boundʳ p (laterʳ⁻¹ q)
    ⊔-upper-boundʳ {y = now y}   (laterˡ _) _ = now-cong
    ⊔-upper-boundʳ {y = later y} (laterˡ p) q =
      later-cong (∞⊔-upper-boundʳ p (laterˡ⁻¹ q))

    ∞⊔-upper-boundʳ : ∀ {i x y z} →
                      ∞LE i x z → ∞LE i y z → ∞LE i y (x ⊔ y)
    force (∞⊔-upper-boundʳ p q) = ⊔-upper-boundʳ (force p) (force q)

  mutual

    -- If x and y have an upper bound, then x ⊔ y is an upper bound
    -- of x.

    ⊔-upper-boundˡ : ∀ {i x y z} →
                     LE i x z → LE i y z → LE i x (x ⊔ y)
    ⊔-upper-boundˡ               now-cong   q = now-cong
    ⊔-upper-boundˡ               (laterʳ p) q = ⊔-upper-boundˡ p (laterʳ⁻¹ q)
    ⊔-upper-boundˡ {y = later y} (laterˡ p) q = later-cong (∞⊔-upper-boundˡ p (laterˡ⁻¹ q))
    ⊔-upper-boundˡ {y = now y}   (laterˡ p) q =
      laterˡ (∞⊔-upper-boundʳ (record { force = λ { {_} → q } }) p)

    ∞⊔-upper-boundˡ : ∀ {i x y z} →
                      ∞LE i x z → ∞LE i y z → ∞LE i x (x ⊔ y)
    force (∞⊔-upper-boundˡ p q) = ⊔-upper-boundˡ (force p) (force q)

  mutual

    -- A variant of the lower/upper bound lemmas.

    ⊔-lower-upper-bound : ∀ {i x y z} →
                          x ⊑ y → LE i y z → LE i y (x ⊔ z)
    ⊔-lower-upper-bound               now-cong   _            = now-cong
    ⊔-lower-upper-bound               (laterʳ p) q            = laterˡ (∞⊔-lower-upper-bound (record { force = p }) (laterˡ⁻¹ q))
    ⊔-lower-upper-bound               (laterˡ p) (laterʳ q)   = laterʳ (⊔-lower-upper-bound (force p) q)
    ⊔-lower-upper-bound {z = now z}   (laterˡ _) q            = q
    ⊔-lower-upper-bound {z = later z} (laterˡ p) (laterˡ q)   = later-cong (∞⊔-lower-upper-bound (∞laterʳ⁻¹ p) (∞laterʳ⁻¹ q))

    ∞⊔-lower-upper-bound : ∀ {i x y z} → x ∞⊑ y → ∞LE i y z → ∞LE i y (x ⊔ z)
    force (∞⊔-lower-upper-bound p q) =
      ⊔-lower-upper-bound (force p) (force q)

  -- If x terminates, then x ⊔ y also terminates.

  ⊔-⇓ˡ : ∀ {i x y} {z : A} →
         Terminates i x z → ∃ λ z′ → Terminates i (x ⊔ y) z′
  ⊔-⇓ˡ               now-cong   = _ , now-cong
  ⊔-⇓ˡ {y = now y}   (laterʳ p) = _ , now-cong
  ⊔-⇓ˡ {y = later y} (laterʳ p) = Σ-map id laterʳ (⊔-⇓ˡ p)

  -- If y terminates, then x ⊔ y also terminates.

  ⊔-⇓ʳ : ∀ {i} x {y} {z : A} →
         Terminates i y z → ∃ λ z′ → Terminates i (x ⊔ y) z′
  ⊔-⇓ʳ (now x)   _          = _ , now-cong
  ⊔-⇓ʳ (later x) now-cong   = _ , now-cong
  ⊔-⇓ʳ (later x) (laterʳ p) = Σ-map id laterʳ (⊔-⇓ʳ (force x) p)

-- Increasing sequences.

Increasing-sequence : ∀ {a} → Set a → Set a
Increasing-sequence A =
  ∃ λ (f : ℕ → Delay A ∞) → ∀ n → f n ⊑ f (suc n)

module _ {a} {A : Set a} where

  -- The tail of an increasing sequence.

  tailˢ : Increasing-sequence A → Increasing-sequence A
  tailˢ = Σ-map (_∘ suc) (_∘ suc)

  -- Later sequence elements are larger.

  later-larger : (s : Increasing-sequence A) →
                 ∀ {m n} → m ≤ n → proj₁ s m ⊑ proj₁ s n
  later-larger s (≤-refl′ refl)   = reflexive _
  later-larger s (≤-step′ p refl) =
    transitive (later-larger s p) (proj₂ s _)

  -- Least upper bounds of increasing sequences.

  mutual

    ⨆ : ∀ {i} → Increasing-sequence A → Delay A i
    ⨆ s = proj₁ s 0 ⊔ later (∞⨆ (tailˢ s))

    ∞⨆ : ∀ {i} → Increasing-sequence A → ∞Delay A i
    force (∞⨆ s) = ⨆ s

  mutual

    -- ⨆ s is smaller than or equal to every upper bound of s.

    ⨆-least-upper-bound :
      ∀ {i} (s : Increasing-sequence A) ub →
      (∀ n → LE i (proj₁ s n) ub) → LE i (⨆ s) ub
    ⨆-least-upper-bound s ub is-ub =
      ⊔-least-upper-bound
        (is-ub 0)
        (laterˡ (∞⨆-least-upper-bound (tailˢ s) ub (is-ub ∘ suc)))

    ∞⨆-least-upper-bound :
      ∀ {i} (s : Increasing-sequence A) ub →
      (∀ n → LE i (proj₁ s n) ub) → ∞LE i (⨆ s) ub
    force (∞⨆-least-upper-bound s ub is-ub) =
      ⨆-least-upper-bound s ub is-ub

  -- If every element in s terminates with a given value, then ⨆ s
  -- terminates with the same value.

  ⨆-⇓ : ∀ {i x} (s : Increasing-sequence A) →
        (∀ n → proj₁ s n ⇓ x) → Terminates i (⨆ s) x
  ⨆-⇓ s s-⇓ =
    ⊑now→⇓→⇓ (⨆-least-upper-bound s _ (λ n → symmetric (s-⇓ n)))
             (proj₂ (⊔-⇓ˡ (s-⇓ 0)))

  mutual

    -- If s has a lower bound, then this is also a lower bound of
    -- ⨆ s.

    ⨆-lower-bound : ∀ {i} (s : Increasing-sequence A) lb →
                    (∀ n → lb ⊑ proj₁ s n) → LE i lb (⨆ s)
    ⨆-lower-bound s (now x)    is-lb = ⨆-⇓ s is-lb
    ⨆-lower-bound s (later lb) is-lb =
      ⊔-lower-bound
        (is-lb 0)
        (later-cong
           (∞⨆-lower-bound (tailˢ s) (force lb) λ n →
              force (laterˡ⁻¹ (transitive (is-lb n) (proj₂ s n)))))

    ∞⨆-lower-bound : ∀ {i} (s : Increasing-sequence A) lb →
                     (∀ n → lb ⊑ proj₁ s n) → ∞LE i lb (⨆ s)
    force (∞⨆-lower-bound s lb is-lb) = ⨆-lower-bound s lb is-lb

  mutual

    -- ⨆ s is an upper bound of s.

    ⨆-upper-bound : ∀ {i} (s : Increasing-sequence A) →
                    ∀ n → LE i (proj₁ s n) (⨆ s)
    ⨆-upper-bound s zero    = ⨆-lower-bound s (proj₁ s 0)
                                (λ n → later-larger s (zero≤ n))
    ⨆-upper-bound s (suc n) = ⊔-lower-upper-bound
                                (later-larger s (zero≤ (suc n)))
                                (laterʳ (⨆-upper-bound (tailˢ s) n))

    ∞⨆-upper-bound : ∀ {i} (s : Increasing-sequence A) →
                     ∀ n → ∞LE i (proj₁ s n) (⨆ s)
    force (∞⨆-upper-bound s n) = ⨆-upper-bound s n
