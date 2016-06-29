------------------------------------------------------------------------
-- The delay monad is a monad up to strong bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad.Monad where

open import Equality.Propositional
open import Prelude hiding (module W)

open import Monad equality-with-J

open import Delay-monad
open import Delay-monad.Strong-bisimilarity as S
open import Delay-monad.Weak-bisimilarity as W

------------------------------------------------------------------------
-- Map, join and bind

mutual

  -- A universe-polymorphic variant of map.

  map′ : ∀ {i a b} {A : Set a} {B : Set b} →
         (A → B) → Delay A i → Delay B i
  map′ f (now x)   = now (f x)
  map′ f (later x) = later (∞map′ f x)

  ∞map′ : ∀ {i a b} {A : Set a} {B : Set b} →
          (A → B) → ∞Delay A i → ∞Delay B i
  force (∞map′ f x) = map′ f (force x)

mutual

  -- Join.

  join : ∀ {i a} {A : Set a} →
         Delay (Delay A i) i → Delay A i
  join (now x)   = x
  join (later x) = later (∞join x)

  ∞join : ∀ {i a} {A : Set a} →
          ∞Delay (Delay A i) i → ∞Delay A i
  force (∞join x) = join (force x)

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ : ∀ {i a b} {A : Set a} {B : Set b} →
         Delay A i → (A → Delay B i) → Delay B i
x >>=′ f = join (map′ f x)

instance

  -- A raw monad instance.

  delay-raw-monad : ∀ {a i} → Raw-monad (λ (A : Set a) → Delay A i)
  Raw-monad.return delay-raw-monad = now
  Raw-monad._>>=_  delay-raw-monad = _>>=′_

------------------------------------------------------------------------
-- Monad laws

left-identity′ :
  ∀ {a b} {A : Set a} {B : Set b} x (f : A → Delay B ∞) →
  return x >>=′ f ∼ f x
left-identity′ x f = S.reflexive (f x)

mutual

  right-identity′ : ∀ {a} {A : Set a} (x : Delay A ∞) →
                    x >>= return ∼ x
  right-identity′ (now x)   = now-cong
  right-identity′ (later x) =
    later-cong (∞right-identity′ (force x))

  ∞right-identity′ : ∀ {a} {A : Set a} (x : Delay A ∞) →
                     x >>= return ∞∼ x
  force (∞right-identity′ x) = right-identity′ x

mutual

  associativity′ :
    ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
    (x : Delay A ∞) (f : A → Delay B ∞) (g : B → Delay C ∞) →
    x >>=′ (λ x → f x >>=′ g) ∼ x >>=′ f >>=′ g
  associativity′ (now x)   f g = S.reflexive (f x >>=′ g)
  associativity′ (later x) f g =
    later-cong (∞associativity′ (force x) f g)

  ∞associativity′ :
    ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
    (x : Delay A ∞) (f : A → Delay B ∞) (g : B → Delay C ∞) →
    x >>=′ (λ x → f x >>=′ g) ∞∼ x >>=′ f >>=′ g
  force (∞associativity′ x f g) = associativity′ x f g

-- The delay monad is a monad (assuming extensionality).

delay-monad :
  ∀ {a} → S.Extensionality a → Monad (λ (A : Set a) → Delay A ∞)
Monad.raw-monad      (delay-monad ext)       = delay-raw-monad
Monad.left-identity  (delay-monad ext) x f   = ext (left-identity′ x f)
Monad.right-identity (delay-monad ext) x     = ext (right-identity′ x)
Monad.associativity  (delay-monad ext) x f g = ext (associativity′ x f g)

------------------------------------------------------------------------
-- The functions map′, join and _>>=′_ preserve strong bisimilarity

mutual

  map-cong-∼ : ∀ {i a b} {A : Set a} {B : Set b}
               (f : A → B) {x y : Delay A ∞} →
               Strongly-bisimilar i x y →
               Strongly-bisimilar i (map′ f x) (map′ f y)
  map-cong-∼ f now-cong       = now-cong
  map-cong-∼ f (later-cong p) = later-cong (∞map-cong-∼ f p)

  ∞map-cong-∼ : ∀ {i a b} {A : Set a} {B : Set b}
                (f : A → B) {x y : Delay A ∞} →
                ∞Strongly-bisimilar i x y →
                ∞Strongly-bisimilar i (map′ f x) (map′ f y)
  force (∞map-cong-∼ f p) = map-cong-∼ f (force p)

mutual

  join-cong-∼ : ∀ {i a} {A : Set a} {x y : Delay (Delay A ∞) ∞} →
                Strongly-bisimilar i x y →
                Strongly-bisimilar i (join x) (join y)
  join-cong-∼ now-cong       = S.reflexive _
  join-cong-∼ (later-cong p) = later-cong (∞join-cong-∼ p)

  ∞join-cong-∼ : ∀ {i a} {A : Set a} {x y : Delay (Delay A ∞) ∞} →
                 ∞Strongly-bisimilar i x y →
                 ∞Strongly-bisimilar i (join x) (join y)
  force (∞join-cong-∼ p) = join-cong-∼ (force p)

mutual

  infixl 5 _>>=-cong-∼_ _∞>>=-cong-∼_

  _>>=-cong-∼_ :
    ∀ {i a b} {A : Set a} {B : Set b}
      {x y : Delay A ∞} {f g : A → Delay B ∞} →
    Strongly-bisimilar i x y →
    (∀ z → Strongly-bisimilar i (f z) (g z)) →
    Strongly-bisimilar i (x >>=′ f) (y >>=′ g)
  now-cong     >>=-cong-∼  q = q _
  later-cong p >>=-cong-∼  q = later-cong (p ∞>>=-cong-∼ q)

  _∞>>=-cong-∼_ :
    ∀ {i a b} {A : Set a} {B : Set b}
      {x y : Delay A ∞} {f g : A → Delay B ∞} →
    ∞Strongly-bisimilar i x y →
    (∀ z → Strongly-bisimilar i (f z) (g z)) →
    ∞Strongly-bisimilar i (x >>=′ f) (y >>=′ g)
  force (p ∞>>=-cong-∼ q) = force p >>=-cong-∼ q

------------------------------------------------------------------------
-- The functions map′, join and _>>=′_ preserve weak bisimilarity

mutual

  map-cong-≈ : ∀ {i a b} {A : Set a} {B : Set b}
               (f : A → B) {x y : Delay A ∞} →
               Weakly-bisimilar i x y →
               Weakly-bisimilar i (map′ f x) (map′ f y)
  map-cong-≈ f now-cong       = now-cong
  map-cong-≈ f (later-cong p) = later-cong (∞map-cong-≈ f p)
  map-cong-≈ f (laterˡ p)     = laterˡ (map-cong-≈ f p)
  map-cong-≈ f (laterʳ p)     = laterʳ (map-cong-≈ f p)

  ∞map-cong-≈ : ∀ {i a b} {A : Set a} {B : Set b}
                (f : A → B) {x y : Delay A ∞} →
                ∞Weakly-bisimilar i x y →
                ∞Weakly-bisimilar i (map′ f x) (map′ f y)
  force (∞map-cong-≈ f p) = map-cong-≈ f (force p)

mutual

  join-cong-≈ : ∀ {i a} {A : Set a} {x y : Delay (Delay A ∞) ∞} →
                Weakly-bisimilar i x y →
                Weakly-bisimilar i (join x) (join y)
  join-cong-≈ now-cong       = W.reflexive _
  join-cong-≈ (later-cong p) = later-cong (∞join-cong-≈ p)
  join-cong-≈ (laterˡ p)     = laterˡ (join-cong-≈ p)
  join-cong-≈ (laterʳ p)     = laterʳ (join-cong-≈ p)

  ∞join-cong-≈ : ∀ {i a} {A : Set a} {x y : Delay (Delay A ∞) ∞} →
                 ∞Weakly-bisimilar i x y →
                 ∞Weakly-bisimilar i (join x) (join y)
  force (∞join-cong-≈ p) = join-cong-≈ (force p)

mutual

  infixl 5 _>>=-cong-≈_ _∞>>=-cong-≈_

  _>>=-cong-≈_ :
    ∀ {i a b} {A : Set a} {B : Set b}
      {x y : Delay A ∞} {f g : A → Delay B ∞} →
    Weakly-bisimilar i x y →
    (∀ z → Weakly-bisimilar i (f z) (g z)) →
    Weakly-bisimilar i (x >>=′ f) (y >>=′ g)
  now-cong     >>=-cong-≈  q = q _
  later-cong p >>=-cong-≈  q = later-cong (p ∞>>=-cong-≈ q)
  laterˡ p     >>=-cong-≈  q = laterˡ (p >>=-cong-≈ q)
  laterʳ p     >>=-cong-≈  q = laterʳ (p >>=-cong-≈ q)

  _∞>>=-cong-≈_ :
    ∀ {i a b} {A : Set a} {B : Set b}
      {x y : Delay A ∞} {f g : A → Delay B ∞} →
    ∞Weakly-bisimilar i x y →
    (∀ z → Weakly-bisimilar i (f z) (g z)) →
    ∞Weakly-bisimilar i (x >>=′ f) (y >>=′ g)
  force (p ∞>>=-cong-≈ q) = force p >>=-cong-≈ q
