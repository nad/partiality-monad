------------------------------------------------------------------------
-- Weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad.Weak-bisimilarity {a} {A : Set a} where

open import Equality.Propositional
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude

open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Function-universe equality-with-J hiding (_∘_)

open import Delay-monad
open import Delay-monad.Strong-bisimilarity as Strong
  using (Strongly-bisimilar; ∞Strongly-bisimilar; _∼_; _∞∼_;
         now-cong; later-cong; force)

-- Weak bisimilarity, defined using mixed induction and coinduction.

mutual

  data Weakly-bisimilar (i : Size) : (x y : Delay A ∞) → Set a where
    now-cong   : ∀ {x} → Weakly-bisimilar i (now x) (now x)
    later-cong : ∀ {x y} →
                 ∞Weakly-bisimilar i (force x) (force y) →
                 Weakly-bisimilar i (later x) (later y)
    laterˡ     : ∀ {x y} →
                 Weakly-bisimilar i (force x) y →
                 Weakly-bisimilar i (later x) y
    laterʳ     : ∀ {x y} →
                 Weakly-bisimilar i x (force y) →
                 Weakly-bisimilar i x (later y)

  record ∞Weakly-bisimilar (i : Size) (x y : Delay A ∞) : Set a where
    coinductive
    field
      force : {j : Size< i} → Weakly-bisimilar j x y

open ∞Weakly-bisimilar public

infix 4 _≈_ _∞≈_

_≈_ : Delay A ∞ → Delay A ∞ → Set a
_≈_ = Weakly-bisimilar ∞

_∞≈_ : Delay A ∞ → Delay A ∞ → Set a
_∞≈_ = ∞Weakly-bisimilar ∞

mutual

  -- Strong bisimilarity is contained in weak bisimilarity.

  ∼→≈ : ∀ {i x y} → Strongly-bisimilar i x y → Weakly-bisimilar i x y
  ∼→≈ now-cong       = now-cong
  ∼→≈ (later-cong p) = later-cong (∞∼→≈ p)

  ∞∼→≈ : ∀ {i x y} → ∞Strongly-bisimilar i x y → ∞Weakly-bisimilar i x y
  force (∞∼→≈ p) = ∼→≈ (force p)

-- Termination predicates.

Terminates : Size → Delay A ∞ → A → Set a
Terminates i x y = Weakly-bisimilar i (now y) x

_⇓_ : Delay A ∞ → A → Set a
_⇓_ = Terminates ∞

-- Terminates i is contained in Terminates ∞.
--
-- Note that Terminates carves out an "inductive fragment" of
-- Weakly-bisimilar: the only "coinductive" constructor, later-cong,
-- does not target Terminates.

terminates→⇓ : ∀ {i x y} → Terminates i x y → x ⇓ y
terminates→⇓ now-cong   = now-cong
terminates→⇓ (laterʳ p) = laterʳ (terminates→⇓ p)

-- The computation never is not terminating.

now≉never : ∀ {i x} → ¬ Terminates i never x
now≉never (laterʳ p) = now≉never p

mutual

  -- If A is uninhabited, then weak bisimilarity is trivial.

  uninhabited→trivial : ∀ {i} → ¬ A → ∀ x y → Weakly-bisimilar i x y
  uninhabited→trivial ¬A (now x)   _         = ⊥-elim (¬A x)
  uninhabited→trivial ¬A (later x) (now y)   = ⊥-elim (¬A y)
  uninhabited→trivial ¬A (later x) (later y) =
    later-cong (∞uninhabited→trivial ¬A x y)

  ∞uninhabited→trivial :
    ∀ {i} → ¬ A → ∀ x y → ∞Weakly-bisimilar i (force x) (force y)
  force (∞uninhabited→trivial ¬A x y) =
    uninhabited→trivial ¬A (force x) (force y)

-- Sometimes one can remove later constructors.

laterʳ⁻¹ : ∀ {i} {j : Size< i} {x y} →
           Weakly-bisimilar i x (later y) →
           Weakly-bisimilar j x (force y)
laterʳ⁻¹ (later-cong p) = laterˡ (force p)
laterʳ⁻¹ (laterʳ p)     = p
laterʳ⁻¹ (laterˡ p)     = laterˡ (laterʳ⁻¹ p)

∞laterʳ⁻¹ : ∀ {i x y} →
            Weakly-bisimilar i x (later y) →
            ∞Weakly-bisimilar i x (force y)
force (∞laterʳ⁻¹ p) = laterʳ⁻¹ p

laterˡ⁻¹ : ∀ {i} {j : Size< i} {x y} →
           Weakly-bisimilar i (later x) y →
           Weakly-bisimilar j (force x) y
laterˡ⁻¹ (later-cong p) = laterʳ (force p)
laterˡ⁻¹ (laterʳ p)     = laterʳ (laterˡ⁻¹ p)
laterˡ⁻¹ (laterˡ p)     = p

∞laterˡ⁻¹ : ∀ {i x y} →
            Weakly-bisimilar i (later x) y →
            ∞Weakly-bisimilar i (force x) y
force (∞laterˡ⁻¹ p) = laterˡ⁻¹ p

later⁻¹ : ∀ {i} {j : Size< i} {x y} →
          Weakly-bisimilar i (later x) (later y) →
          Weakly-bisimilar j (force x) (force y)
later⁻¹ (later-cong p) = force p
later⁻¹ (laterʳ p)     = laterˡ⁻¹ p
later⁻¹ (laterˡ p)     = laterʳ⁻¹ p

∞later⁻¹ : ∀ {i x y} →
           Weakly-bisimilar i (later x) (later y) →
           ∞Weakly-bisimilar i (force x) (force y)
force (∞later⁻¹ p) = later⁻¹ p

mutual

  -- Weak bisimilarity is reflexive.

  reflexive : (x : Delay A ∞) → x ≈ x
  reflexive (now x)   = now-cong
  reflexive (later x) = later-cong (∞reflexive (force x))

  ∞reflexive : (x : Delay A ∞) → x ∞≈ x
  force (∞reflexive x) = reflexive x

mutual

  -- Weak bisimilarity is symmetric.

  symmetric : ∀ {i} {x y : Delay A ∞} →
              Weakly-bisimilar i x y →
              Weakly-bisimilar i y x
  symmetric now-cong       = now-cong
  symmetric (later-cong p) = later-cong (∞symmetric p)
  symmetric (laterˡ p)     = laterʳ (symmetric p)
  symmetric (laterʳ p)     = laterˡ (symmetric p)

  ∞symmetric : ∀ {i} {x y : Delay A ∞} →
               ∞Weakly-bisimilar i x y →
               ∞Weakly-bisimilar i y x
  force (∞symmetric p) = symmetric (force p)

-- The termination relation respects weak bisimilarity.

⇓-respects-≈ : ∀ {i} {x y : Delay A ∞} {z} →
               Terminates i x z → x ≈ y → Terminates i y z
⇓-respects-≈ now-cong   now-cong   = now-cong
⇓-respects-≈ (laterʳ p) q          = ⇓-respects-≈ p (laterˡ⁻¹ q)
⇓-respects-≈ p          (laterʳ q) = laterʳ (⇓-respects-≈ p q)

-- The previous result can be made size-preserving in the second
-- argument iff A is uninhabited.

size-preserving-⇓-respects-≈⇔uninhabited :
  (∀ {i} {x y : Delay A ∞} {z} →
   x ⇓ z → Weakly-bisimilar i x y → Terminates i y z) ⇔
  ¬ A
size-preserving-⇓-respects-≈⇔uninhabited = record
  { to   = Now-trans              ↝⟨ (λ trans → now≈never (λ {i} → trans {i})) ⟩
           (∀ x → now x ≈ never)  ↝⟨ (λ hyp x → now≉never (hyp x)) ⟩
           ¬ A                    □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Now-trans        □
  }
  where
  Now-trans = ∀ {i} {x y : Delay A ∞} {z} →
              x ⇓ z → Weakly-bisimilar i x y → Terminates i y z

  mutual

    now≈never : Now-trans → ∀ {i} x →
                Weakly-bisimilar i (now x) never
    now≈never trans x =
      trans (laterʳ {y = record { force = now x }} (reflexive (now x)))
            (later-cong (∞now≈never trans x))

    ∞now≈never : Now-trans → ∀ {i} x →
                 ∞Weakly-bisimilar i (now x) never
    force (∞now≈never trans x) = now≈never trans x

mutual

  -- Weak bisimilarity is transitive.

  later-trans : ∀ {x} {y z : Delay A ∞} →
                later x ≈ y → y ≈ z → later x ≈ z
  later-trans p          (later-cong q) = later-cong (∞transitive (later⁻¹ p) (force q))
  later-trans p          (laterˡ q)     = later-trans (laterʳ⁻¹ p) q
  later-trans p          (laterʳ q)     = later-cong (∞transitive (laterˡ⁻¹ p) q)
  later-trans (laterˡ p) q              = laterˡ (transitive p q)

  transitive : {x y z : Delay A ∞} →
               x ≈ y → y ≈ z → x ≈ z
  transitive {x = now x}   p q = ⇓-respects-≈ p q
  transitive {x = later x} p q = later-trans p q

  ∞transitive : {x y z : Delay A ∞} →
                x ≈ y → y ≈ z → x ∞≈ z
  force (∞transitive p q) = transitive p q

-- There is a transitivity proof that preserves the size of the
-- second argument iff A is uninhabited.

size-preserving-transitivityʳ⇔uninhabited :
  (∀ {i} {x y z : Delay A ∞} →
   x ≈ y → Weakly-bisimilar i y z → Weakly-bisimilar i x z) ⇔
  ¬ A
size-preserving-transitivityʳ⇔uninhabited = record
  { to   = Trans      ↝⟨ (λ trans {_ _ _ _} now-z≈x x≈y → trans now-z≈x x≈y) ⟩
           Now-trans  ↝⟨ _⇔_.to size-preserving-⇓-respects-≈⇔uninhabited ⟩□
           ¬ A        □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Trans            □
  }
  where
  Trans     = ∀ {i} {x y z : Delay A ∞} →
              x ≈ y → Weakly-bisimilar i y z → Weakly-bisimilar i x z
  Now-trans = ∀ {i} {x y : Delay A ∞} {z} →
              x ⇓ z → Weakly-bisimilar i x y → Terminates i y z

-- There is a transitivity proof that preserves the size of the
-- first argument iff A is uninhabited.

size-preserving-transitivityˡ⇔uninhabited :
  (∀ {i} {x y z : Delay A ∞} →
   Weakly-bisimilar i x y → y ≈ z → Weakly-bisimilar i x z) ⇔
  ¬ A
size-preserving-transitivityˡ⇔uninhabited =
  (∀ {i} {x y z : Delay A ∞} →
   Weakly-bisimilar i x y → y ≈ z → Weakly-bisimilar i x z)  ↝⟨ record { to   = λ trans {_ _ _ _} p q →
                                                                                  symmetric (trans (symmetric q) (symmetric p))
                                                                       ; from = λ trans {_ _ _ _} p q →
                                                                                  symmetric (trans (symmetric q) (symmetric p))
                                                                       } ⟩
  (∀ {i} {x y z : Delay A ∞} →
   x ≈ y → Weakly-bisimilar i y z → Weakly-bisimilar i x z)  ↝⟨ size-preserving-transitivityʳ⇔uninhabited ⟩□

  ¬ A                                                        □

-- Some size-preserving variants of transitivity.

mutual

  transitive-∼≈ :
    ∀ {i} {x y z : Delay A ∞} →
    x ∼ y → Weakly-bisimilar i y z → Weakly-bisimilar i x z
  transitive-∼≈ now-cong       q              = q
  transitive-∼≈ (later-cong p) (later-cong q) = later-cong (∞transitive-∼≈ p q)
  transitive-∼≈ (later-cong p) (laterˡ q)     = laterˡ (transitive-∼≈ (force p) q)
  transitive-∼≈ p              (laterʳ q)     = laterʳ (transitive-∼≈ p q)

  ∞transitive-∼≈ :
    ∀ {i} {x y z : Delay A ∞} →
    x ∞∼ y → ∞Weakly-bisimilar i y z → ∞Weakly-bisimilar i x z
  force (∞transitive-∼≈ p q) = transitive-∼≈ (force p) (force q)

transitive-≈∼ :
  ∀ {i} {x y z : Delay A ∞} →
  Weakly-bisimilar i x y → y ∼ z → Weakly-bisimilar i x z
transitive-≈∼ p q =
  symmetric (transitive-∼≈ (Strong.symmetric q) (symmetric p))

-- Some equational reasoning combinators.

infix  -1 finally-≈ _∎≈
infixr -2 _≈⟨_⟩_ _≈⟨_⟩∞_ _≈⟨⟩_ _∼⟨_⟩≈_ _≡⟨_⟩≈_ _≡⟨_⟩∞≈_ _≳⟨⟩_

_∎≈ : ∀ {i} (x : Delay A ∞) → Weakly-bisimilar i x x
_∎≈ = reflexive

_≈⟨_⟩_ : ∀ {i} (x : Delay A ∞) {y z} →
         Weakly-bisimilar i x y → y ∼ z → Weakly-bisimilar i x z
_ ≈⟨ p ⟩ q = transitive-≈∼ p q

_≈⟨_⟩∞_ : ∀ {i} (x : Delay A ∞) {y z} →
          ∞Weakly-bisimilar i x y → y ∼ z → ∞Weakly-bisimilar i x z
force (_ ≈⟨ p ⟩∞ q) = transitive-≈∼ (force p) q

_≈⟨⟩_ : ∀ {i} (x : Delay A ∞) {y} →
        Weakly-bisimilar i x y → Weakly-bisimilar i x y
_ ≈⟨⟩ p = p

_∼⟨_⟩≈_ : ∀ {i} (x : Delay A ∞) {y z} →
          x ∼ y → Weakly-bisimilar i y z → Weakly-bisimilar i x z
_ ∼⟨ p ⟩≈ q = transitive-∼≈ p q

_≡⟨_⟩≈_ : ∀ {i} (x : Delay A ∞) {y z} →
          x ≡ y → Weakly-bisimilar i y z → Weakly-bisimilar i x z
_≡⟨_⟩≈_ {i} _ p q = subst (λ x → Weakly-bisimilar i x _) (sym p) q

_≡⟨_⟩∞≈_ : ∀ {i} (x : Delay A ∞) {y z} →
           x ≡ y → ∞Weakly-bisimilar i y z → ∞Weakly-bisimilar i x z
force (_ ≡⟨ p ⟩∞≈ q) = _ ≡⟨ p ⟩≈ force q

_≳⟨⟩_ : ∀ {i} (x : Delay A ∞) {y} →
        Weakly-bisimilar i (drop-later x) y → Weakly-bisimilar i x y
now x   ≳⟨⟩ p = p
later x ≳⟨⟩ p = laterˡ p

finally-≈ : ∀ {i} (x y : Delay A ∞) →
            Weakly-bisimilar i x y → Weakly-bisimilar i x y
finally-≈ _ _ p = p

syntax finally-≈ x y p = x ≈⟨ p ⟩∎ y ∎

-- The function laterˡ⁻¹ can be made size-preserving iff A is
-- uninhabited.

size-preserving-laterˡ⁻¹⇔uninhabited :
  (∀ {i x y} →
   Weakly-bisimilar i (later x) y →
   Weakly-bisimilar i (force x) y) ⇔
  ¬ A
size-preserving-laterˡ⁻¹⇔uninhabited = record
  { to   = Laterˡ⁻¹               ↝⟨ (λ laterˡ⁻¹ x → now≈never (λ {i} → laterˡ⁻¹ {i}) x) ⟩
           (∀ x → now x ≈ never)  ↝⟨ (λ hyp x → now≉never (hyp x)) ⟩□
           ¬ A                    □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _} _ → trivial _ _) ⟩□
           Laterˡ⁻¹         □
  }
  where
  Laterˡ⁻¹ = ∀ {i x y} →
             Weakly-bisimilar i (later x) y →
             Weakly-bisimilar i (force x) y

  module _ (laterˡ⁻¹ : Laterˡ⁻¹) (x : A) where

    mutual

      now≈never : ∀ {i} → Weakly-bisimilar i (now x) never
      now≈never = laterˡ⁻¹ {x = record { force = now x }}
                           (later-cong ∞now≈never)

      ∞now≈never : ∀ {i} → ∞Weakly-bisimilar i (now x) never
      force ∞now≈never = now≈never

-- The function laterʳ⁻¹ can be made size-preserving iff A is
-- uninhabited.

size-preserving-laterʳ⁻¹⇔uninhabited :
  (∀ {i x y} →
   Weakly-bisimilar i x (later y) →
   Weakly-bisimilar i x (force y)) ⇔
  ¬ A
size-preserving-laterʳ⁻¹⇔uninhabited =
  (∀ {i x y} →
   Weakly-bisimilar i x (later y) → Weakly-bisimilar i x (force y))  ↝⟨ record { to   = λ laterʳ⁻¹ → symmetric ∘ laterʳ⁻¹ ∘ symmetric
                                                                               ; from = λ laterˡ⁻¹ → symmetric ∘ laterˡ⁻¹ ∘ symmetric
                                                                               } ⟩
  (∀ {i x y} →
   Weakly-bisimilar i (later x) y → Weakly-bisimilar i (force x) y)  ↝⟨ size-preserving-laterˡ⁻¹⇔uninhabited ⟩□

  ¬ A                                                                □

-- However, the following size-preserving variant of laterʳ⁻¹ and
-- laterˡ⁻¹ can be defined.

laterˡʳ⁻¹ :
  ∀ {i} {x y : ∞Delay A ∞} →
  Weakly-bisimilar i (later x) (force y) →
  Weakly-bisimilar i (force x) (later y) →
  Weakly-bisimilar i (force x) (force y)
laterˡʳ⁻¹ p q = laterˡʳ⁻¹′ p q refl refl
  where
  ∞laterˡʳ⁻¹′ :
    ∀ {i x′ y′} {x y : ∞Delay A ∞} →
    ∞Weakly-bisimilar i x′ (force y) →
    ∞Weakly-bisimilar i (force x) y′ →
    later x ≡ x′ → later y ≡ y′ →
    ∞Weakly-bisimilar i (force x) (force y)
  force (∞laterˡʳ⁻¹′ p q refl refl) = laterˡʳ⁻¹ (force p) (force q)

  laterˡʳ⁻¹′ :
    ∀ {i x′ y′} {x y : ∞Delay A ∞} →
    Weakly-bisimilar i (later x) y′ →
    Weakly-bisimilar i x′ (later y) →
    x′ ≡ force x → y′ ≡ force y →
    Weakly-bisimilar i x′ y′
  laterˡʳ⁻¹′ (later-cong p) (later-cong q) x′≡  y′≡  = later-cong (∞laterˡʳ⁻¹′ p             q             x′≡ y′≡)
  laterˡʳ⁻¹′ (laterʳ p)     (later-cong q) x′≡  y′≡  = later-cong (∞laterˡʳ⁻¹′ (∞laterˡ⁻¹ p) q             x′≡ y′≡)
  laterˡʳ⁻¹′ (later-cong p) (laterˡ q)     x′≡  y′≡  = later-cong (∞laterˡʳ⁻¹′ p             (∞laterʳ⁻¹ q) x′≡ y′≡)
  laterˡʳ⁻¹′ (laterʳ p)     (laterˡ q)     x′≡  y′≡  = later-cong (∞laterˡʳ⁻¹′ (∞laterˡ⁻¹ p) (∞laterʳ⁻¹ q) x′≡ y′≡)
  laterˡʳ⁻¹′ (laterˡ p)     _              refl refl = p
  laterˡʳ⁻¹′ _              (laterʳ q)     refl y′≡  = subst (Weakly-bisimilar _ _) (sym y′≡) q

∞laterˡʳ⁻¹ :
  ∀ {i} {x y : ∞Delay A ∞} →
  ∞Weakly-bisimilar i (later x) (force y) →
  ∞Weakly-bisimilar i (force x) (later y) →
  ∞Weakly-bisimilar i (force x) (force y)
force (∞laterˡʳ⁻¹ p q) = laterˡʳ⁻¹ (force p) (force q)

-- The notion of weak bisimilarity defined here is not necessarily
-- propositional.

¬-≈-proposition : ¬ (∀ {x y} → Is-proposition (x ≈ y))
¬-≈-proposition =
  (∀ {x y} → Is-proposition (x ≈ y))  ↝⟨ (λ prop → _⇔_.to propositional⇔irrelevant (prop {x = never} {y = never})) ⟩
  Proof-irrelevant (never ≈ never)    ↝⟨ (λ irr → irr _ _) ⟩
  proof₁ ≡ proof₂                     ↝⟨ (λ ()) ⟩□
  ⊥₀                                  □
  where
  mutual
    proof₁ : never ≈ never
    proof₁ = later-cong ∞proof₁

    ∞proof₁ : never ∞≈ never
    force ∞proof₁ = proof₁

  proof₂ : never ≈ never
  proof₂ = laterˡ proof₁

-- However, if A is a set, then the termination predicate is
-- propositional.

Terminates-propositional :
  Is-set A → ∀ {i x y} → Is-proposition (Terminates i x y)
Terminates-propositional A-set {i} =
  _⇔_.from propositional⇔irrelevant (λ p q → irr p q refl)
  where
  irr :
    ∀ {x y y′}
    (p : Weakly-bisimilar i (now y)  x)
    (q : Weakly-bisimilar i (now y′) x)
    (y≡y′ : y ≡ y′) →
    subst (flip (Weakly-bisimilar i) x ∘ now) y≡y′ p ≡ q
  irr         (laterʳ p) (laterʳ q) refl = cong laterʳ (irr p q refl)
  irr {y = y} now-cong   now-cong   y≡y  =
    subst (flip (Weakly-bisimilar i) (now y) ∘ now) y≡y  now-cong  ≡⟨ cong (λ eq → subst _ eq _) (_⇔_.to set⇔UIP A-set y≡y refl) ⟩
    subst (flip (Weakly-bisimilar i) (now y) ∘ now) refl now-cong  ≡⟨⟩
    now-cong                                                       ∎

-- An alternative definition of weak bisimilarity (basically the one
-- used in the paper).
--
-- This definition is logically equivalent to the one above, see
-- Delay-monad.Partial-order.≈⇔≈′.

infix 4 _≈′_

_≈′_ : Delay A ∞ → Delay A ∞ → Set a
x ≈′ y = ∀ z → x ⇓ z ⇔ y ⇓ z

-- If A is a set, then the alternative definition of weak bisimilarity
-- is propositional.

≈′-propositional : Is-set A → ∀ {x y} → Is-proposition (x ≈′ y)
≈′-propositional A-set =
  Π-closure ext 1 λ _ →
  ⇔-closure ext 1 (Terminates-propositional A-set)
                  (Terminates-propositional A-set)
