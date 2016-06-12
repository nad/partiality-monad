------------------------------------------------------------------------
-- A monad-like structure
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad.Sized.Monad where

open import Prelude

open import Delay-monad.Sized
open import Delay-monad.Sized.Strong-bisimilarity as S
open import Delay-monad.Sized.Weak-bisimilarity

-- Return.

return : ∀ {i a} {A : Size → Set a} → A i → Delay A i
return = now

mutual

  -- Map. Note the function argument's type.

  map : ∀ {i a b} {A : Size → Set a} {B : Size → Set b} →
        ({j : Size< (ssuc i)} → A j → B j) → Delay A i → Delay B i
  map f (now x)   = now (f x)
  map f (later x) = later (∞map f x)

  ∞map : ∀ {i a b} {A : Size → Set a} {B : Size → Set b} →
        ({j : Size< (ssuc i)} → A j → B j) → ∞Delay A i → ∞Delay B i
  force (∞map f x) = map f (force x)

mutual

  -- The map function preserves strong bisimilarity.

  map-cong-∼ : ∀ {i a b} {A : Size → Set a} {B : Size → Set b}
               (f : ∀ {i} → A i → B i) {x y : Delay A ∞} →
               Strongly-bisimilar i x y →
               Strongly-bisimilar i (map f x) (map f y)
  map-cong-∼ f now-cong       = now-cong
  map-cong-∼ f (later-cong p) = later-cong (∞map-cong-∼ f p)

  ∞map-cong-∼ : ∀ {i a b} {A : Size → Set a} {B : Size → Set b}
                (f : ∀ {i} → A i → B i) {x y : Delay A ∞} →
                ∞Strongly-bisimilar i x y →
                ∞Strongly-bisimilar i (map f x) (map f y)
  force (∞map-cong-∼ f p) = map-cong-∼ f (force p)

mutual

  -- The map function preserves weak bisimilarity.

  map-cong-≈ : ∀ {i a b} {A : Size → Set a} {B : Size → Set b}
               (f : ∀ {i} → A i → B i) {x y : Delay A ∞} →
               Weakly-bisimilar i x y →
               Weakly-bisimilar i (map f x) (map f y)
  map-cong-≈ f now-cong       = now-cong
  map-cong-≈ f (later-cong p) = later-cong (∞map-cong-≈ f p)
  map-cong-≈ f (laterˡ p)     = laterˡ (map-cong-≈ f p)
  map-cong-≈ f (laterʳ p)     = laterʳ (map-cong-≈ f p)

  ∞map-cong-≈ : ∀ {i a b} {A : Size → Set a} {B : Size → Set b}
                (f : ∀ {i} → A i → B i) {x y : Delay A ∞} →
                ∞Weakly-bisimilar i x y →
                ∞Weakly-bisimilar i (map f x) (map f y)
  force (∞map-cong-≈ f p) = map-cong-≈ f (force p)

mutual

  -- Join.

  join : ∀ {i a} {A : Size → Set a} →
         Delay (Delay A) i → Delay A i
  join (now x)   = x
  join (later x) = later (∞join x)

  ∞join : ∀ {i a} {A : Size → Set a} →
          ∞Delay (Delay A) i → ∞Delay A i
  force (∞join x) = join (force x)

-- Bind. Note the function argument's type.

infixl 5 _>>=_

_>>=_ : ∀ {i a b} {A : Size → Set a} {B : Size → Set b} →
        Delay A i → ({j : Size< (ssuc i)} → A j → Delay B j) → Delay B i
x >>= f = join (map f x)

-- The monad laws.

left-identity :
  ∀ {a b} {A : Size → Set a} {B : Size → Set b}
  x (f : ∀ {i} → A i → Delay B i) →
  return x >>= f ∼ f x
left-identity x f = S.reflexive (f x)

mutual

  right-identity : ∀ {a} {A : Size → Set a} (x : Delay A ∞) →
                   x >>= return ∼ x
  right-identity (now x)   = now-cong
  right-identity (later x) =
    later-cong (∞right-identity (force x))

  ∞right-identity : ∀ {a} {A : Size → Set a} (x : Delay A ∞) →
                    x >>= return ∞∼ x
  force (∞right-identity x) = right-identity x

mutual

  associativity :
    ∀ {a b c} {A : Size → Set a} {B : Size → Set b} {C : Size → Set c} →
    (x : Delay A ∞) (f : ∀ {i} → A i → Delay B i)
    (g : ∀ {i} → B i → Delay C i) →
    x >>= (λ x → f x >>= g) ∼ x >>= f >>= g
  associativity (now x)   f g = S.reflexive (f x >>= g)
  associativity (later x) f g =
    later-cong (∞associativity (force x) f g)

  ∞associativity :
    ∀ {a b c} {A : Size → Set a} {B : Size → Set b} {C : Size → Set c} →
    (x : Delay A ∞) (f : ∀ {i} → A i → Delay B i)
    (g : ∀ {i} → B i → Delay C i) →
    x >>= (λ x → f x >>= g) ∞∼ x >>= f >>= g
  force (∞associativity x f g) = associativity x f g
