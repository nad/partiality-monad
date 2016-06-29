------------------------------------------------------------------------
-- The "always true" predicate, □
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad.Always where

open import Prelude

open import Delay-monad
open import Delay-monad.Monad

-- The "always true" predicate, □.

mutual

  data □ {a p} {A : Set a} (i : Size) (P : A → Set p) :
         Delay A ∞ → Set (a ⊔ p) where
    □-now   : ∀ {x} → P x → □ i P (now x)
    □-later : ∀ {x} → ∞□ i P (force x) → □ i P (later x)

  record ∞□ {a p} {A : Set a} (i : Size) (P : A → Set p)
            (x : Delay A ∞) : Set (a ⊔ p) where
    coinductive
    field
      force : {j : Size< i} → □ j P x

open ∞□ public

mutual

  -- □ is closed, in a certain sense, under bind.

  □->>= :
    ∀ {i a b p q}
      {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q}
      {x : Delay A ∞} {f : A → Delay B ∞} →
    □ i P x → (∀ {x} → P x → □ i Q (f x)) → □ i Q (x >>=′ f)
  □->>= (□-now P-x)   □-f = □-f P-x
  □->>= (□-later □-x) □-f = □-later (∞□->>= □-x □-f)

  ∞□->>= :
    ∀ {i a b p q}
      {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q}
      {x : Delay A ∞} {f : A → Delay B ∞} →
    ∞□ i P x → (∀ {x} → P x → □ i Q (f x)) → ∞□ i Q (x >>=′ f)
  force (∞□->>= □-x □-f) = □->>= (force □-x) □-f
