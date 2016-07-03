------------------------------------------------------------------------
-- A partial order
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad.Partial-order {a} {A : Set a} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (module W)

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J

open import Delay-monad
open import Delay-monad.Weak-bisimilarity as W
  using (Weakly-bisimilar; ∞Weakly-bisimilar; _≈_; force)

mutual

  -- An ordering relation.
  --
  -- Capretta defines a logically equivalent relation in "General
  -- Recursion via Coinductive Types".
  --
  -- Benton, Kennedy and Varming define a relation that is perhaps
  -- logically equivalent in "Some Domain Theory and Denotational
  -- Semantics in Coq".

  data LE (i : Size) : Delay A ∞ → Delay A ∞ → Set a where
    now-cong : ∀ {x} → LE i (now x) (now x)
    laterʳ   : ∀ {x y} → LE i x (force y) → LE i x (later y)
    laterˡ   : ∀ {x y} → ∞LE i (force x) y → LE i (later x) y

  record ∞LE (i : Size) (x y : Delay A ∞) : Set a where
    coinductive
    field
      force : {j : Size< i} → LE j x y

open ∞LE public

infix 4 _⊑_ _∞⊑_

_⊑_ : Delay A ∞ → Delay A ∞ → Set a
_⊑_ = LE ∞

_∞⊑_ : Delay A ∞ → Delay A ∞ → Set a
_∞⊑_ = ∞LE ∞

-- Some variants of the LE constructors.

later-cong : ∀ {i x y} →
             ∞LE i (force x) (force y) → LE i (later x) (later y)
later-cong p = laterʳ (laterˡ p)

∞laterʳ : ∀ {i x y} → ∞LE i x (force y) → ∞LE i x (later y)
force (∞laterʳ p) = laterʳ (force p)

laterˡ′ : ∀ {i x y} → LE i (force x) y → LE i (later x) y
laterˡ′ p = laterˡ (record { force = λ { {_} → p } })

-- Termination predicates.

Terminates : Size → Delay A ∞ → A → Set a
Terminates i x y = LE i (now y) x

∞Terminates : Size → Delay A ∞ → A → Set a
∞Terminates i x y = ∞LE i (now y) x

_⇓_ : Delay A ∞ → A → Set a
_⇓_ = Terminates ∞

-- If x terminates with the values y and z, then y is equal to z.

⇓→⇓→≡ : ∀ {i x y z} → Terminates i x y → Terminates i x z → y ≡ z
⇓→⇓→≡ now-cong   now-cong   = refl
⇓→⇓→≡ (laterʳ p) (laterʳ q) = ⇓→⇓→≡ p q

-- If x is smaller than or equal to now y, and x terminates, then
-- x terminates with the value y.

⊑now→⇓→⇓ : ∀ {i x} {y z : A} →
           x ⊑ now y → Terminates i x z → Terminates i x y
⊑now→⇓→⇓ now-cong   now-cong   = now-cong
⊑now→⇓→⇓ (laterˡ p) (laterʳ q) = laterʳ (⊑now→⇓→⇓ (force p) q)

-- The notion of termination defined here is isomorphic to the one
-- defined in Delay-monad.Weak-bisimilarity.

⇓↔⇓ : ∀ {i x y} → Terminates i x y ↔ W.Terminates i x y
⇓↔⇓ = record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  to : ∀ {i x y} → Terminates i x y → W.Terminates i x y
  to now-cong   = W.now-cong
  to (laterʳ p) = W.laterʳ (to p)

  from : ∀ {i x y} → W.Terminates i x y → Terminates i x y
  from W.now-cong   = now-cong
  from (W.laterʳ p) = laterʳ (from p)

  from∘to : ∀ {i x y} (p : Terminates i x y) → from (to p) ≡ p
  from∘to now-cong   = refl
  from∘to (laterʳ p) = cong laterʳ (from∘to p)

  to∘from : ∀ {i x y} (p : W.Terminates i x y) → to (from p) ≡ p
  to∘from W.now-cong   = refl
  to∘from (W.laterʳ p) = cong W.laterʳ (to∘from p)

mutual

  -- The computation never is smaller than or equal to all other
  -- computations.

  never⊑ : ∀ {i} x → LE i never x
  never⊑ (now x)   = laterˡ (∞never⊑ (now x))
  never⊑ (later x) = later-cong (∞never⊑ (force x))

  ∞never⊑ : ∀ {i} x → ∞LE i never x
  force (∞never⊑ x) = never⊑ x

-- The computation never does not terminate.

now⋢never : ∀ {i x} → ¬ Terminates i never x
now⋢never (laterʳ p) = now⋢never p

-- One can remove later constructors.

laterˡ⁻¹ : ∀ {i x y} → LE i (later x) y → ∞LE i (force x) y
laterˡ⁻¹ (laterʳ p) = ∞laterʳ (laterˡ⁻¹ p)
laterˡ⁻¹ (laterˡ p) = p

mutual

  laterʳ⁻¹ : ∀ {i x y} → LE i x (later y) → LE i x (force y)
  laterʳ⁻¹ (laterʳ p) = p
  laterʳ⁻¹ (laterˡ p) = laterˡ (∞laterʳ⁻¹ p)

  ∞laterʳ⁻¹ : ∀ {i x y} → ∞LE i x (later y) → ∞LE i x (force y)
  force (∞laterʳ⁻¹ p) = laterʳ⁻¹ (force p)

later-cong⁻¹ :
  ∀ {i x y} → LE i (later x) (later y) → ∞LE i (force x) (force y)
later-cong⁻¹ p = ∞laterʳ⁻¹ (laterˡ⁻¹ p)

mutual

  -- Weak bisimilarity is contained in the ordering relation.

  ≈→⊑ : ∀ {i x y} → Weakly-bisimilar i x y → LE i x y
  ≈→⊑ W.now-cong       = now-cong
  ≈→⊑ (W.later-cong p) = later-cong (∞≈→⊑ p)
  ≈→⊑ (W.laterˡ p)     = laterˡ′ (≈→⊑ p)
  ≈→⊑ (W.laterʳ p)     = laterʳ (≈→⊑ p)

  ∞≈→⊑ : ∀ {i x y} → ∞Weakly-bisimilar i x y → ∞LE i x y
  force (∞≈→⊑ p) = ≈→⊑ (force p)

mutual

  -- The ordering relation is antisymmetric (with respect to weak
  -- bisimilarity).

  antisymmetric : ∀ {i x y} →
                  LE i x y → LE i y x → Weakly-bisimilar i x y
  antisymmetric {x = now x}   {y = now .x}  now-cong   _          = W.now-cong
  antisymmetric {x = now x}   {y = later y} (laterʳ p) q          = W.laterʳ (_↔_.to ⇓↔⇓ p)
  antisymmetric {x = later x} {y = now y}   p          (laterʳ q) = W.laterˡ (W.symmetric (_↔_.to ⇓↔⇓ q))
  antisymmetric {x = later x} {y = later y} p          q          =
    W.later-cong (∞antisymmetric (later-cong⁻¹ p) (later-cong⁻¹ q))

  ∞antisymmetric : ∀ {i x y} →
                   ∞LE i x y → ∞LE i y x → ∞Weakly-bisimilar i x y
  force (∞antisymmetric p q) = antisymmetric (force p) (force q)

-- An alternative characterisation of weak bisimilarity.

≈⇔⊑×⊒ : ∀ {i x y} → Weakly-bisimilar i x y ⇔ (LE i x y × LE i y x)
≈⇔⊑×⊒ = record
  { to   = λ p → ≈→⊑ p , ≈→⊑ (W.symmetric p)
  ; from = uncurry antisymmetric
  }

mutual

  -- The ordering relation is reflexive.

  reflexive : ∀ {i} x → LE i x x
  reflexive (now x)   = now-cong
  reflexive (later x) = later-cong (∞reflexive (force x))

  ∞reflexive : ∀ {i} x → ∞LE i x x
  force (∞reflexive x) = reflexive x

mutual

  -- Certain instances of symmetry also hold.

  symmetric : ∀ {i} {x : A} {y} →
              Terminates i y x → LE i y (now x)
  symmetric now-cong   = now-cong
  symmetric (laterʳ p) = laterˡ (∞symmetric p)

  ∞symmetric : ∀ {i} {x : A} {y} →
               Terminates i y x → ∞LE i y (now x)
  force (∞symmetric p) = symmetric p

mutual

  -- The ordering relation is transitive.

  transitive : ∀ {i} {x y z : Delay A ∞} →
               LE i x y → y ⊑ z → LE i x z
  transitive p          now-cong   = p
  transitive p          (laterʳ q) = laterʳ (transitive p q)
  transitive (laterʳ p) (laterˡ q) = transitive p (force q)
  transitive (laterˡ p) q          = laterˡ (∞transitive p q)

  ∞transitive : ∀ {i} {x y z : Delay A ∞} →
                ∞LE i x y → y ⊑ z → ∞LE i x z
  force (∞transitive p q) = transitive (force p) q

-- The termination relation respects weak bisimilarity.

⇓-respects-≈ : ∀ {i x y z} → Terminates i x z → x ≈ y → Terminates i y z
⇓-respects-≈ now-cong   q = ≈→⊑ q
⇓-respects-≈ (laterʳ p) q = ⇓-respects-≈ p (W.laterˡ⁻¹ q)

-- The ordering relation respects weak bisimilarity.

transitive-≈⊑ : ∀ {i x y z} → Weakly-bisimilar i x y → y ⊑ z → LE i x z
transitive-≈⊑ p q = transitive (≈→⊑ p) q

mutual

  transitive-⊑≈ : ∀ {i x y z} → x ⊑ y → y ≈ z → LE i x z
  transitive-⊑≈ p          W.now-cong       = p
  transitive-⊑≈ (laterʳ p) (W.later-cong q) = laterʳ (transitive-⊑≈ p (force q))
  transitive-⊑≈ (laterˡ p) q                = laterˡ (∞transitive-⊑≈ p q)
  transitive-⊑≈ (laterʳ p) (W.laterˡ q)     = transitive-⊑≈ p q
  transitive-⊑≈ p          (W.laterʳ q)     = laterʳ (transitive-⊑≈ p q)

  ∞transitive-⊑≈ : ∀ {i x y z} → x ∞⊑ y → y ≈ z → ∞LE i x z
  force (∞transitive-⊑≈ p q) = transitive-⊑≈ (force p) q

-- There is a transitivity-like function that produces an ordering
-- proof from one weak bisimilarity proof and one ordering proof,
-- in such a way that the size of the ordering proof is preserved,
-- iff A is uninhabited.

other-transitivity⇔uninhabited :
  (∀ {i} {x y z : Delay A ∞} → x ≈ y → LE i y z → LE i x z) ⇔
  ¬ A
other-transitivity⇔uninhabited = record
  { to   = Trans                  ↝⟨ (λ trans x → never-top-element (λ {i} → trans {i}) (record { force = now x })) ⟩
           (∀ x → now x ⊑ never)  ↝⟨ (λ hyp x → now⋢never (hyp x)) ⟩
           ¬ A                    □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ⊑ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Trans            □
  }
  where
  Trans = ∀ {i} {x y z : Delay A ∞} → x ≈ y → LE i y z → LE i x z

  mutual

    never-top-element :
      Trans → ∀ {i} (x : ∞Delay _ _) → LE i (force x) never
    never-top-element trans x =
      trans (W.laterʳ {y = x} (W.reflexive (force x)))
            (later-cong (∞never-top-element trans x))

    ∞never-top-element :
      Trans → ∀ {i} (x : ∞Delay _ _) → ∞LE i (force x) never
    force (∞never-top-element trans x) = never-top-element trans x

  mutual

    uninhabited→trivial : ∀ {i} → ¬ A → ∀ x y → LE i x y
    uninhabited→trivial ¬A (now x)   _         = ⊥-elim (¬A x)
    uninhabited→trivial ¬A (later x) (now y)   = ⊥-elim (¬A y)
    uninhabited→trivial ¬A (later x) (later y) =
      later-cong (∞uninhabited→trivial ¬A x y)

    ∞uninhabited→trivial :
      ∀ {i} → ¬ A → ∀ x y → ∞LE i (force x) (force y)
    force (∞uninhabited→trivial ¬A x y) =
      uninhabited→trivial ¬A (force x) (force y)

-- An alternative characterisation of the ordering relation.
--
-- Capretta proves a similar result in "General Recursion via
-- Coinductive Types".

⊑⇔⇓→⇓ : ∀ {x y} → x ⊑ y ⇔ (∀ z → x ⇓ z → y ⇓ z)
⊑⇔⇓→⇓ = record
  { to   = to
  ; from = from _
  }
  where
  to : ∀ {x y} → x ⊑ y → ∀ z → x ⇓ z → y ⇓ z
  to p          z now-cong   = p
  to (laterʳ p) z q          = laterʳ (to p z q)
  to (laterˡ p) z (laterʳ q) = to (force p) z q

  mutual

    from : ∀ x {y} → (∀ z → x ⇓ z → y ⇓ z) → x ⊑ y
    from (now x)   p = p x now-cong
    from (later x) p = laterˡ (∞from (force x) (λ z q → p z (laterʳ q)))

    ∞from : ∀ x {y} → (∀ z → x ⇓ z → y ⇓ z) → x ∞⊑ y
    force (∞from x p) = from x p
