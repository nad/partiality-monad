------------------------------------------------------------------------
-- Weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad.Weak-bisimilarity {a} {A : Set a} where

open import Equality.Propositional
open import H-level.Truncation.Propositional as Trunc
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Double-negation equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Monad equality-with-J

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

infix 4 _⇓_

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
--
-- This function cannot be made size-preserving in its second argument
-- (unless A is uninhabited), see below.

⇓-respects-≈ : ∀ {i} {x y : Delay A ∞} {z} →
               Terminates i x z → x ≈ y → Terminates i y z
⇓-respects-≈ now-cong   now-cong   = now-cong
⇓-respects-≈ (laterʳ p) q          = ⇓-respects-≈ p (laterˡ⁻¹ q)
⇓-respects-≈ p          (laterʳ q) = laterʳ (⇓-respects-≈ p q)

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

-- Some size-preserving variants of transitivity.
--
-- Many size-preserving variants cannot be defined (unless A is
-- uninhabited), see below.

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
infixr -2 _≈⟨_⟩_ _≈⟨_⟩∼_ _≈⟨_⟩∞∼_ _≈⟨⟩_ _∼⟨_⟩≈_ _≡⟨_⟩≈_ _≡⟨_⟩∞≈_ _≳⟨⟩_

_∎≈ : ∀ {i} (x : Delay A ∞) → Weakly-bisimilar i x x
_∎≈ = reflexive

_≈⟨_⟩_ : ∀ (x : Delay A ∞) {y z} →
         x ≈ y → y ≈ z → x ≈ z
_ ≈⟨ p ⟩ q = transitive p q

_≈⟨_⟩∼_ : ∀ {i} (x : Delay A ∞) {y z} →
         Weakly-bisimilar i x y → y ∼ z → Weakly-bisimilar i x z
_ ≈⟨ p ⟩∼ q = transitive-≈∼ p q

_≈⟨_⟩∞∼_ : ∀ {i} (x : Delay A ∞) {y z} →
          ∞Weakly-bisimilar i x y → y ∼ z → ∞Weakly-bisimilar i x z
force (_ ≈⟨ p ⟩∞∼ q) = transitive-≈∼ (force p) q

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

-- The following size-preserving variant of laterʳ⁻¹ and laterˡ⁻¹ can
-- be defined.
--
-- Several other variants cannot be defined (unless A is uninhabited),
-- see below.

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

mutual

  -- If a computation does not terminate, then it is weakly bisimilar
  -- to never.

  ¬⇓→⇑ : ∀ {i} x → ¬ (∃ λ y → x ⇓ y) → Weakly-bisimilar i never x
  ¬⇓→⇑ (now x)   ¬⇓ = ⊥-elim (¬⇓ (_ , now-cong))
  ¬⇓→⇑ (later x) ¬⇓ = later-cong (∞¬⇓→⇑ _ (¬⇓ ∘ Σ-map id laterʳ))

  ∞¬⇓→⇑ : ∀ {i} x → ¬ (∃ λ y → x ⇓ y) → ∞Weakly-bisimilar i never x
  force (∞¬⇓→⇑ x ¬⇓) = ¬⇓→⇑ x ¬⇓

-- In the double-negation monad every computation is weakly
-- bisimilar to either never or now something.

¬¬[⇑⊎⇓] : ∀ x → ¬¬ (never ≈ x ⊎ ∃ λ y → x ⇓ y)
¬¬[⇑⊎⇓] x = [ inj₂ , inj₁ ∘ ¬⇓→⇑ _ ] ⟨$⟩ excluded-middle

-- Every computation is weakly bisimilar to either never or
-- now something (assuming excluded middle). See also
-- Delay-monad.Partial-order.⇑⊎⇓.

∥⇑∥⊎∥⇓∥ : Excluded-middle a → ∀ x → ∥ never ≈ x ∥ ⊎ ∥ (∃ λ y → x ⇓ y) ∥
∥⇑∥⊎∥⇓∥ em x =
  Excluded-middle→Double-negation-elimination em
    (⊎-closure-propositional
       (Trunc.rec (Π-closure ext 1 λ _ → ⊥-propositional) λ x⇑ →
        Trunc.rec ⊥-propositional λ { (y , x⇓y) →
          now≉never (now y  ≈⟨ x⇓y ⟩
                     x      ≈⟨ symmetric x⇑ ⟩∎
                     never  ∎) })
       truncation-is-proposition
       truncation-is-proposition)
    (⊎-map ∣_∣ ∣_∣ ⟨$⟩ ¬¬[⇑⊎⇓] x)

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

-- If x terminates with y and z, then y is equal to z.

termination-value-unique :
  ∀ {i x y z} → Terminates i x y → Terminates i x z → y ≡ z
termination-value-unique now-cong   now-cong   = refl
termination-value-unique (laterʳ p) (laterʳ q) =
  termination-value-unique p q

-- If A is a set, then ∃ λ y → x ⇓ y is propositional.

∃-Terminates-propositional :
  Is-set A → ∀ {i x} → Is-proposition (∃ (Terminates i x))
∃-Terminates-propositional A-set =
  _⇔_.from propositional⇔irrelevant λ where
    (y₁ , x⇓y₁) (y₂ , x⇓y₂) →
      Σ-≡,≡→≡
        (termination-value-unique x⇓y₁ x⇓y₂)
        (_⇔_.to propositional⇔irrelevant
           (Terminates-propositional A-set) _ _)

------------------------------------------------------------------------
-- Alternative definitions of weak bisimilarity

-- An alternative definition of weak bisimilarity (basically the one
-- used in the paper).
--
-- This definition is logically equivalent to the one above, see
-- Delay-monad.Partial-order.≈⇔≈′.

infix 4 _≈′_

_≈′_ : Delay A ∞ → Delay A ∞ → Set a
x ≈′ y = ∀ z → x ⇓ z ⇔ y ⇓ z

-- If A is a set, then this alternative definition of weak
-- bisimilarity is propositional.

≈′-propositional : Is-set A → ∀ {x y} → Is-proposition (x ≈′ y)
≈′-propositional A-set =
  Π-closure ext 1 λ _ →
  ⇔-closure ext 1 (Terminates-propositional A-set)
                  (Terminates-propositional A-set)

-- Another alternative definition of weak bisimilarity, basically the
-- one given by Capretta in "General Recursion via Coinductive Types".

mutual

  data Weakly-bisimilar″ (i : Size) :
         Delay A ∞ → Delay A ∞ → Set a where
    both-terminate : ∀ {x y v} → x ⇓ v → y ⇓ v → Weakly-bisimilar″ i x y
    later-cong     : ∀ {x y} →
                     ∞Weakly-bisimilar″ i (force x) (force y) →
                     Weakly-bisimilar″ i (later x) (later y)

  record ∞Weakly-bisimilar″ (i : Size) (x y : Delay A ∞) : Set a where
    coinductive
    field
      force : {j : Size< i} → Weakly-bisimilar″ j x y

open ∞Weakly-bisimilar″ public

infix 4 _≈″_

_≈″_ : Delay A ∞ → Delay A ∞ → Set a
_≈″_ = Weakly-bisimilar″ ∞

-- If A is inhabited, then this definition is not propositional.

¬-≈″-propositional : A → ¬ (∀ {x y} → Is-proposition (x ≈″ y))
¬-≈″-propositional x =
  (∀ {x y} → Is-proposition (x ≈″ y))  ↝⟨ (λ prop → prop) ⟩
  Is-proposition (y ≈″ y)              ↝⟨ _⇔_.to propositional⇔irrelevant ⟩
  Proof-irrelevant (y ≈″ y)            ↝⟨ (_$ _) ∘ (_$ _) ⟩
  proof₁ ≡ proof₂                      ↝⟨ (λ ()) ⟩□
  ⊥                                    □
  where
  ∞y : ∞Delay A ∞
  force ∞y = now x

  y : Delay A ∞
  y = later ∞y

  proof₁ : y ≈″ y
  proof₁ = both-terminate (laterʳ now-cong) (laterʳ now-cong)

  ∞proof₂ : ∞Weakly-bisimilar″ ∞ (now x) (now x)
  force ∞proof₂ = both-terminate now-cong now-cong

  proof₂ : y ≈″ y
  proof₂ = later-cong ∞proof₂

-- The last definition of weak bisimilarity given above is pointwise
-- logically equivalent to the first one. Note that the proof is
-- size-preserving.
--
-- (Given suitable notions of extensionality the two definitions are
-- not pointwise isomorphic, because given such assumptions there is
-- only one proof of never ≈″ never, but multiple proofs of
-- never ≈ never. However, there is no Agda proof of this claim in
-- this module.)

Weakly-bisimilar⇔Weakly-bisimilar″ :
  ∀ {i x y} → Weakly-bisimilar i x y ⇔ Weakly-bisimilar″ i x y
Weakly-bisimilar⇔Weakly-bisimilar″ = record { to = to; from = from }
  where
  mutual

    laterˡ′ : ∀ {i x x′ y} →
              x′ ≡ force x →
              Weakly-bisimilar″ i x′ y →
              Weakly-bisimilar″ i (later x) y
    laterˡ′ eq (both-terminate x⇓ y⇓) = both-terminate
                                          (laterʳ (subst (_⇓ _) eq x⇓))
                                          y⇓
    laterˡ′ eq (later-cong p)         = later-cong (∞laterˡ′ eq p)

    ∞laterˡ′ : ∀ {i x x′ y} →
               later x′ ≡ x →
               ∞Weakly-bisimilar″ i (force x′) y →
               ∞Weakly-bisimilar″ i x y
    force (∞laterˡ′ refl p) = laterˡ′ refl (force p)

  mutual

    laterʳ′ : ∀ {i x y y′} →
              y′ ≡ force y →
              Weakly-bisimilar″ i x y′ →
              Weakly-bisimilar″ i x (later y)
    laterʳ′ eq (both-terminate x⇓ y⇓) = both-terminate
                                          x⇓
                                          (laterʳ (subst (_⇓ _) eq y⇓))
    laterʳ′ eq (later-cong p)         = later-cong (∞laterʳ′ eq p)

    ∞laterʳ′ : ∀ {i x y y′} →
               later y′ ≡ y →
               ∞Weakly-bisimilar″ i x (force y′) →
               ∞Weakly-bisimilar″ i x y
    force (∞laterʳ′ refl p) = laterʳ′ refl (force p)

  mutual

    to : ∀ {i x y} → Weakly-bisimilar i x y → Weakly-bisimilar″ i x y
    to now-cong       = both-terminate now-cong now-cong
    to (later-cong p) = later-cong (∞to p)
    to (laterˡ p)     = laterˡ′ refl (to p)
    to (laterʳ p)     = laterʳ′ refl (to p)

    ∞to : ∀ {i x y} → ∞Weakly-bisimilar i x y → ∞Weakly-bisimilar″ i x y
    force (∞to p) = to (force p)

  mutual

    from : ∀ {i x y} → Weakly-bisimilar″ i x y → Weakly-bisimilar i x y
    from (both-terminate x⇓v y⇓v) = from⇓ x⇓v y⇓v
    from (later-cong p)           = later-cong (∞from p)

    from⇓ : ∀ {i x y v} → x ⇓ v → y ⇓ v → Weakly-bisimilar i x y
    from⇓ now-cong   now-cong   = now-cong
    from⇓ p          (laterʳ q) = laterʳ (from⇓ p q)
    from⇓ (laterʳ p) q          = laterˡ (from⇓ p q)

    ∞from :
      ∀ {i x y} → ∞Weakly-bisimilar″ i x y → ∞Weakly-bisimilar i x y
    force (∞from p) = from (force p)

------------------------------------------------------------------------
-- Lemmas stating that certain size-preserving functions can be
-- defined iff A is uninhabited

mutual

  -- A lemma used in several of the proofs below: If A is uninhabited,
  -- then weak bisimilarity is trivial.

  uninhabited→trivial : ∀ {i} → ¬ A → ∀ x y → Weakly-bisimilar i x y
  uninhabited→trivial ¬A (now x)   _         = ⊥-elim (¬A x)
  uninhabited→trivial ¬A (later x) (now y)   = ⊥-elim (¬A y)
  uninhabited→trivial ¬A (later x) (later y) =
    later-cong (∞uninhabited→trivial ¬A x y)

  ∞uninhabited→trivial :
    ∀ {i} → ¬ A → ∀ x y → ∞Weakly-bisimilar i (force x) (force y)
  force (∞uninhabited→trivial ¬A x y) =
    uninhabited→trivial ¬A (force x) (force y)

-- A variant of laterˡ⁻¹ in which one occurrence of weak bisimilarity
-- is replaced by strong bisimilarity, and both arguments are
-- specialised, can be made size-preserving iff A is uninhabited.
--
-- This lemma is used to prove all the results below (directly or
-- indirectly).

Laterˡ⁻¹-∼≈ =
  ∀ {i x} →
  Strongly-bisimilar i (later (record { force = now x })) never →
  Weakly-bisimilar i (now x) never

size-preserving-laterˡ⁻¹-∼≈⇔uninhabited : Laterˡ⁻¹-∼≈ ⇔ ¬ A
size-preserving-laterˡ⁻¹-∼≈⇔uninhabited = record
  { to   = Laterˡ⁻¹-∼≈  ↝⟨ (λ laterˡ⁻¹-∼≈ x → contradiction (laterˡ⁻¹-∼≈ {_}) x ∞) ⟩□
           ¬ A          □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _} _ → trivial _ _) ⟩□
           Laterˡ⁻¹-∼≈      □
  }
  where

  module _ (laterˡ⁻¹-∼≈ : Laterˡ⁻¹-∼≈) (x : A) where

    mutual

      now≈never : ∀ {i} → Weakly-bisimilar i (now x) never
      now≈never = laterˡ⁻¹-∼≈ (later-cong ∞now∼never)

      ∞now∼never : ∀ {i} → ∞Strongly-bisimilar i (now x) never
      force ∞now∼never {j = j} = ⊥-elim (contradiction j)

      contradiction : Size → ⊥
      contradiction i = now≉never (now≈never {i = i})

-- A variant of laterʳ⁻¹ in which one occurrence of weak bisimilarity
-- is replaced by strong bisimilarity, and both arguments are
-- specialised, can be made size-preserving iff A is uninhabited.

Laterʳ⁻¹-∼≈ =
  ∀ {i x} →
  Strongly-bisimilar i never (later (record { force = now x })) →
  Weakly-bisimilar i never (now x)

size-preserving-laterʳ⁻¹-∼≈⇔uninhabited : Laterʳ⁻¹-∼≈ ⇔ ¬ A
size-preserving-laterʳ⁻¹-∼≈⇔uninhabited =
  Laterʳ⁻¹-∼≈  ↝⟨ record { to   = λ laterʳ⁻¹ → symmetric ∘ laterʳ⁻¹ ∘ Strong.symmetric
                         ; from = λ laterˡ⁻¹ → symmetric ∘ laterˡ⁻¹ ∘ Strong.symmetric
                         } ⟩
  Laterˡ⁻¹-∼≈  ↝⟨ size-preserving-laterˡ⁻¹-∼≈⇔uninhabited ⟩□

  ¬ A          □

-- The function laterˡ⁻¹ can be made size-preserving iff A is
-- uninhabited.

Laterˡ⁻¹ = ∀ {i x y} →
           Weakly-bisimilar i (later x) y →
           Weakly-bisimilar i (force x) y

size-preserving-laterˡ⁻¹⇔uninhabited : Laterˡ⁻¹ ⇔ ¬ A
size-preserving-laterˡ⁻¹⇔uninhabited = record
  { to   = Laterˡ⁻¹     ↝⟨ _∘ ∼→≈ ⟩
           Laterˡ⁻¹-∼≈  ↝⟨ _⇔_.to size-preserving-laterˡ⁻¹-∼≈⇔uninhabited ⟩□
           ¬ A          □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _} _ → trivial _ _) ⟩□
           Laterˡ⁻¹         □
  }

-- The function laterʳ⁻¹ can be made size-preserving iff A is
-- uninhabited.

Laterʳ⁻¹ = ∀ {i x y} →
           Weakly-bisimilar i x (later y) →
           Weakly-bisimilar i x (force y)

size-preserving-laterʳ⁻¹⇔uninhabited : Laterʳ⁻¹ ⇔ ¬ A
size-preserving-laterʳ⁻¹⇔uninhabited =
  Laterʳ⁻¹  ↝⟨ record { to   = λ laterʳ⁻¹ → symmetric ∘ laterʳ⁻¹ ∘ symmetric
                      ; from = λ laterˡ⁻¹ → symmetric ∘ laterˡ⁻¹ ∘ symmetric
                      } ⟩
  Laterˡ⁻¹  ↝⟨ size-preserving-laterˡ⁻¹⇔uninhabited ⟩□

  ¬ A       □

-- A variant of ⇓-respects-≈ in which _≈_ is replaced by _∼_ can be
-- made size-preserving in the second argument iff A is uninhabited.

⇓-Respects-∼ʳ = ∀ {i} {x y : Delay A ∞} {z} →
                x ⇓ z → Strongly-bisimilar i x y → Terminates i y z

size-preserving-⇓-respects-∼ʳ⇔uninhabited : ⇓-Respects-∼ʳ ⇔ ¬ A
size-preserving-⇓-respects-∼ʳ⇔uninhabited = record
  { to   = ⇓-Respects-∼ʳ  ↝⟨ (λ resp → resp (laterʳ now-cong)) ⟩
           Laterˡ⁻¹-∼≈    ↝⟨ _⇔_.to size-preserving-laterˡ⁻¹-∼≈⇔uninhabited ⟩
           ¬ A            □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           ⇓-Respects-∼ʳ    □
  }

-- The lemma ⇓-respects-≈ can be made size-preserving in the second
-- argument iff A is uninhabited.

⇓-Respects-≈ʳ = ∀ {i} {x y : Delay A ∞} {z} →
                x ⇓ z → Weakly-bisimilar i x y → Terminates i y z

size-preserving-⇓-respects-≈ʳ⇔uninhabited : ⇓-Respects-≈ʳ ⇔ ¬ A
size-preserving-⇓-respects-≈ʳ⇔uninhabited = record
  { to   = ⇓-Respects-≈ʳ  ↝⟨ (λ resp x⇓z → resp x⇓z ∘ ∼→≈) ⟩
           ⇓-Respects-∼ʳ  ↝⟨ _⇔_.to size-preserving-⇓-respects-∼ʳ⇔uninhabited ⟩□
           ¬ A            □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           ⇓-Respects-≈ʳ    □
  }

-- There is a transitivity proof that preserves the size of the
-- second argument iff A is uninhabited.

Transitivityʳ = ∀ {i} {x y z : Delay A ∞} →
                x ≈ y → Weakly-bisimilar i y z → Weakly-bisimilar i x z

size-preserving-transitivityʳ⇔uninhabited : Transitivityʳ ⇔ ¬ A
size-preserving-transitivityʳ⇔uninhabited = record
  { to   = Transitivityʳ  ↝⟨ (λ trans → trans) ⟩
           ⇓-Respects-≈ʳ  ↝⟨ _⇔_.to size-preserving-⇓-respects-≈ʳ⇔uninhabited ⟩□
           ¬ A            □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivityʳ    □
  }

-- There is a transitivity proof that preserves the size of the
-- first argument iff A is uninhabited.

Transitivityˡ = ∀ {i} {x y z : Delay A ∞} →
                Weakly-bisimilar i x y → y ≈ z → Weakly-bisimilar i x z

size-preserving-transitivityˡ⇔uninhabited : Transitivityˡ ⇔ ¬ A
size-preserving-transitivityˡ⇔uninhabited =
  Transitivityˡ  ↝⟨ record { to   = λ trans {_ _ _ _} p q →
                                      symmetric (trans (symmetric q) (symmetric p))
                           ; from = λ trans {_ _ _ _} p q →
                                      symmetric (trans (symmetric q) (symmetric p))
                           } ⟩
  Transitivityʳ  ↝⟨ size-preserving-transitivityʳ⇔uninhabited ⟩□

  ¬ A            □

-- There is a variant of transitivity-≈∼ that preserves the size of
-- the second argument iff A is uninhabited.

Transitivity-≈∼ʳ =
  ∀ {i} {x y z : Delay A ∞} →
  x ≈ y → Strongly-bisimilar i y z → Weakly-bisimilar i x z

size-preserving-transitivity-≈∼ʳ⇔uninhabited : Transitivity-≈∼ʳ ⇔ ¬ A
size-preserving-transitivity-≈∼ʳ⇔uninhabited = record
  { to   = Transitivity-≈∼ʳ  ↝⟨ (λ trans → trans) ⟩
           ⇓-Respects-∼ʳ     ↝⟨ _⇔_.to size-preserving-⇓-respects-∼ʳ⇔uninhabited ⟩
           ¬ A               □
  ; from = ¬ A               ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)   ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-≈∼ʳ  □
  }

-- There is a variant of transitivity-∼≈ that preserves the size of
-- the first argument iff A is uninhabited.

Transitivity-∼≈ˡ =
  ∀ {i} {x y z : Delay A ∞} →
  Strongly-bisimilar i x y → y ≈ z → Weakly-bisimilar i x z

size-preserving-transitivity-∼≈ˡ⇔uninhabited : Transitivity-∼≈ˡ ⇔ ¬ A
size-preserving-transitivity-∼≈ˡ⇔uninhabited =
  Transitivity-∼≈ˡ  ↝⟨ record { to   = λ trans {_ _ _ _} p q →
                                         symmetric (trans (Strong.symmetric q) (symmetric p))
                              ; from = λ trans {_ _ _ _} p q →
                                         symmetric (trans (symmetric q) (Strong.symmetric p))
                              } ⟩
  Transitivity-≈∼ʳ  ↝⟨ size-preserving-transitivity-≈∼ʳ⇔uninhabited ⟩□

  ¬ A               □
