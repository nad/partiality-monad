------------------------------------------------------------------------
-- Weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Prelude

module Delay-monad.Sized.Weak-bisimilarity {a} {A : Size → Set a} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)

open import H-level equality-with-J
open import Function-universe equality-with-J

open import Delay-monad.Sized
open import Delay-monad.Sized.Strong-bisimilarity as Strong
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

Terminates : Size → Delay A ∞ → A ∞ → Set a
Terminates i x y = Weakly-bisimilar i (now y) x

∞Terminates : Size → Delay A ∞ → A ∞ → Set a
∞Terminates i x y = ∞Weakly-bisimilar i (now y) x

_⇓_ : Delay A ∞ → A ∞ → Set a
_⇓_ = Terminates ∞

-- Terminates i is contained in Terminates ∞.

terminates→⇓ : ∀ {i x y} → Terminates i x y → x ⇓ y
terminates→⇓ now-cong   = now-cong
terminates→⇓ (laterʳ p) = laterʳ (terminates→⇓ p)

-- The computation never is not terminating.

now≉never : ∀ {i x} → ¬ Terminates i never x
now≉never (laterʳ p) = now≉never p

mutual

  -- If A ∞ is uninhabited, then weak bisimilarity is trivial.

  uninhabited→trivial : ∀ {i} → ¬ A ∞ → ∀ x y → Weakly-bisimilar i x y
  uninhabited→trivial ¬A (now x)   _         = ⊥-elim (¬A x)
  uninhabited→trivial ¬A (later x) (now y)   = ⊥-elim (¬A y)
  uninhabited→trivial ¬A (later x) (later y) =
    later-cong (∞uninhabited→trivial ¬A x y)

  ∞uninhabited→trivial :
    ∀ {i} → ¬ A ∞ → ∀ x y → ∞Weakly-bisimilar i (force x) (force y)
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

-- If the previous result can be made size-preserving in the second
-- argument, then ∀ i → A i is uninhabited.

Now-trans = ∀ {i} {x y : Delay A ∞} {z} →
            x ⇓ z → Weakly-bisimilar i x y → Terminates i y z

size-preserving-⇓-respects-≈→uninhabited : Now-trans → ¬ (∀ i → A i)
size-preserving-⇓-respects-≈→uninhabited =
  Now-trans                              ↝⟨ (λ trans → now≈never (λ {i} → trans {i})) ⟩
  ((x : ∀ i → A i) → now (x ∞) ≈ never)  ↝⟨ (λ hyp x → now≉never (hyp x)) ⟩□
  ¬ (∀ i → A i)                          □
  where
  mutual

    now≈never : Now-trans → ∀ {i} (x : ∀ i → A i) →
                Weakly-bisimilar i (now (x ∞)) never
    now≈never trans x =
      trans (laterʳ {y = record { force = now (x _) }}
                    (reflexive (now (x ∞))))
            (later-cong (∞now≈never trans x))

    ∞now≈never : Now-trans → ∀ {i} (x : ∀ i → A i) →
                 ∞Weakly-bisimilar i (now (x ∞)) never
    force (∞now≈never trans x) = now≈never trans x

-- If A ∞ is uninhabited, then there is a size-preserving transitivity
-- proof of the kind mentioned above.

uninhabited→size-preserving-⇓-respects-≈ : ¬ A ∞ → Now-trans
uninhabited→size-preserving-⇓-respects-≈ =
  ¬ A ∞            ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
  Now-trans        □

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

-- Having a transitivity proof that preserves the size of the first
-- argument is logically equivalent to having one that preserves the
-- size of the second argument.

Transˡ = ∀ {i} {x y z : Delay A ∞} →
         Weakly-bisimilar i x y → y ≈ z → Weakly-bisimilar i x z

Transʳ = ∀ {i} {x y z : Delay A ∞} →
         x ≈ y → Weakly-bisimilar i y z → Weakly-bisimilar i x z

size-preserving-transitivityˡ⇔size-preserving-transitivityʳ :
  Transˡ ⇔ Transʳ
size-preserving-transitivityˡ⇔size-preserving-transitivityʳ = record
  { to   = λ trans p q → symmetric (trans (symmetric q) (symmetric p))
  ; from = λ trans p q → symmetric (trans (symmetric q) (symmetric p))
  }

-- If there is a transitivity proof that preserves the size of the
-- second argument, then ∀ i → A i is uninhabited.

size-preserving-transitivityʳ→uninhabited : Transʳ → ¬ (∀ i → A i)
size-preserving-transitivityʳ→uninhabited =
  Transʳ                                 ↝⟨ (λ trans x → ≈never (λ {i} → trans {i})
                                                                (record { force = now (x _) })) ⟩
  ((x : ∀ i → A i) → now (x ∞) ≈ never)  ↝⟨ (λ hyp x → now≉never (hyp x)) ⟩□
  ¬ (∀ i → A i)                          □
  where
  mutual

    ≈never : Transʳ → ∀ {i} (x : ∞Delay _ _) →
             Weakly-bisimilar i (force x) never
    ≈never trans x =
      trans (laterʳ {y = x} (reflexive (force x)))
            (later-cong (∞≈never trans x))

    ∞≈never : Transʳ → ∀ {i} (x : ∞Delay _ _) →
              ∞Weakly-bisimilar i (force x) never
    force (∞≈never trans x) = ≈never trans x

-- If A ∞ is uninhabited, then there is a transitivity proof that
-- preserves the size of the second argument.

uninhabited→size-preserving-transitivityʳ : ¬ A ∞ → Transʳ
uninhabited→size-preserving-transitivityʳ =
  ¬ A ∞            ↝⟨ uninhabited→trivial ⟩
  (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
  Transʳ           □

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

drop-later : Delay A ∞ → Delay A ∞
drop-later (now x)   = now x
drop-later (later x) = force x

_≳⟨⟩_ : ∀ {i} (x : Delay A ∞) {y} →
        Weakly-bisimilar i (drop-later x) y → Weakly-bisimilar i x y
now x   ≳⟨⟩ p = p
later x ≳⟨⟩ p = laterˡ p

finally-≈ : ∀ {i} (x y : Delay A ∞) →
            Weakly-bisimilar i x y → Weakly-bisimilar i x y
finally-≈ _ _ p = p

syntax finally-≈ x y p = x ≈⟨ p ⟩∎ y ∎

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