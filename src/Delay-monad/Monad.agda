------------------------------------------------------------------------
-- The delay monad is a monad up to strong bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad.Monad where

open import Prelude

open import Delay-monad
open import Delay-monad.Strong-bisimilarity as S
open import Delay-monad.Weak-bisimilarity

-- Return.

return : ∀ {a} {A : Set a} → A → Delay A ∞
return = now

mutual

  -- Map.

  map : ∀ {i a b} {A : Set a} {B : Set b} →
        (A → B) → Delay A i → Delay B i
  map f (now x)   = now (f x)
  map f (later x) = later (∞map f x)

  ∞map : ∀ {i a b} {A : Set a} {B : Set b} →
         (A → B) → ∞Delay A i → ∞Delay B i
  force (∞map f x) = map f (force x)

mutual

  -- Join.

  join : ∀ {i a} {A : Set a} →
         Delay (Delay A i) i → Delay A i
  join (now x)   = x
  join (later x) = later (∞join x)

  ∞join : ∀ {i a} {A : Set a} →
          ∞Delay (Delay A i) i → ∞Delay A i
  force (∞join x) = join (force x)

-- Bind.

infixl 5 _>>=_

_>>=_ : ∀ {i a b} {A : Set a} {B : Set b} →
        Delay A i → (A → Delay B i) → Delay B i
x >>= f = join (map f x)

-- The monad laws.

left-identity :
  ∀ {a b} {A : Set a} {B : Set b} x (f : A → Delay B ∞) →
  return x >>= f ∼ f x
left-identity x f = S.reflexive (f x)

mutual

  right-identity : ∀ {a} {A : Set a} (x : Delay A ∞) →
                   x >>= return ∼ x
  right-identity (now x)   = now-cong
  right-identity (later x) =
    later-cong (∞right-identity (force x))

  ∞right-identity : ∀ {a} {A : Set a} (x : Delay A ∞) →
                    x >>= return ∞∼ x
  force (∞right-identity x) = right-identity x

mutual

  associativity :
    ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
    (x : Delay A ∞) (f : A → Delay B ∞) (g : B → Delay C ∞) →
    x >>= (λ x → f x >>= g) ∼ x >>= f >>= g
  associativity (now x)   f g = S.reflexive (f x >>= g)
  associativity (later x) f g =
    later-cong (∞associativity (force x) f g)

  ∞associativity :
    ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
    (x : Delay A ∞) (f : A → Delay B ∞) (g : B → Delay C ∞) →
    x >>= (λ x → f x >>= g) ∞∼ x >>= f >>= g
  force (∞associativity x f g) = associativity x f g

mutual

  -- The map function preserves strong bisimilarity.

  map-cong-∼ : ∀ {i a b} {A : Set a} {B : Set b}
               (f : A → B) {x y : Delay A ∞} →
               Strongly-bisimilar i x y →
               Strongly-bisimilar i (map f x) (map f y)
  map-cong-∼ f now-cong       = now-cong
  map-cong-∼ f (later-cong p) = later-cong (∞map-cong-∼ f p)

  ∞map-cong-∼ : ∀ {i a b} {A : Set a} {B : Set b}
                (f : A → B) {x y : Delay A ∞} →
                ∞Strongly-bisimilar i x y →
                ∞Strongly-bisimilar i (map f x) (map f y)
  force (∞map-cong-∼ f p) = map-cong-∼ f (force p)

mutual

  -- The map function preserves weak bisimilarity.

  map-cong-≈ : ∀ {i a b} {A : Set a} {B : Set b}
               (f : A → B) {x y : Delay A ∞} →
               Weakly-bisimilar i x y →
               Weakly-bisimilar i (map f x) (map f y)
  map-cong-≈ f now-cong       = now-cong
  map-cong-≈ f (later-cong p) = later-cong (∞map-cong-≈ f p)
  map-cong-≈ f (laterˡ p)     = laterˡ (map-cong-≈ f p)
  map-cong-≈ f (laterʳ p)     = laterʳ (map-cong-≈ f p)

  ∞map-cong-≈ : ∀ {i a b} {A : Set a} {B : Set b}
                (f : A → B) {x y : Delay A ∞} →
                ∞Weakly-bisimilar i x y →
                ∞Weakly-bisimilar i (map f x) (map f y)
  force (∞map-cong-≈ f p) = map-cong-≈ f (force p)
