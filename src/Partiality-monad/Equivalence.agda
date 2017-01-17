------------------------------------------------------------------------
-- The partiality monads in Partiality-monad.Inductive and
-- Partiality-monad.Coinductive are pointwise equivalent, for sets,
-- assuming extensionality, propositional extensionality and countable
-- choice
------------------------------------------------------------------------

{-# OPTIONS --without-K --rewriting #-}

module Partiality-monad.Equivalence {a} {A : Set a} where

open import Equality.Propositional
open import H-level.Truncation.Propositional as Trunc
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (⊥; ↑)
open import Quotient.HIT as Quotient hiding ([_])

open import Bijection equality-with-J using (_↔_)
open import Embedding equality-with-J
  using (Is-embedding; Injective≃Is-embedding)
open import Equivalence equality-with-J as Eq
  using (_≃_; Is-equivalence)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Injection equality-with-J using (Injective)
open import Univalence-axiom equality-with-J

import Delay-monad as D
open import Delay-monad.Alternative as A using (_↓_; _↑)
import Delay-monad.Strong-bisimilarity as S
import Delay-monad.Weak-bisimilarity as W
import Partiality-monad.Coinductive as C
import Partiality-monad.Coinductive.Alternative as CA
open import Partiality-monad.Inductive as I
  hiding (_⊥; _⊑_; Increasing-sequence; _⇓_)
open import Partiality-monad.Inductive.Alternative-order
open import Partiality-monad.Inductive.Eliminators

------------------------------------------------------------------------
-- A function from the partiality monad defined in
-- Partiality-monad.Coinductive.Alternative to the inductive
-- partiality monad

-- Turns potential values into partial values.

Maybe→⊥ : Maybe A → A I.⊥
Maybe→⊥ nothing  = never
Maybe→⊥ (just y) = now y

-- Maybe→⊥ is monotone.

Maybe→⊥-mono : ∀ {x y} → A.LE x y → Maybe→⊥ x I.⊑ Maybe→⊥ y
Maybe→⊥-mono (inj₁ refl) = ⊑-refl _
Maybe→⊥-mono (inj₂ (refl , y≢n)) = never⊑ _

-- Maybe→⊥ can be used to turn increasing sequences of one kind into
-- increasing sequences of another kind.

Delay→Inc-seq : A.Delay A → I.Increasing-sequence A
Delay→Inc-seq (f , inc) = Maybe→⊥ ∘ f , Maybe→⊥-mono ∘ inc

-- Turns increasing sequences of potential values into partial values.

Delay→⊥ : A.Delay A → A I.⊥
Delay→⊥ = ⨆ ∘ Delay→Inc-seq

-- Delay→⊥ is monotone (if A is a set).

Delay→⊥-mono :
  Is-set A → ∀ x y → x A.∥⊑∥ y → Delay→⊥ x I.⊑ Delay→⊥ y
Delay→⊥-mono A-set x@(f , _) y@(g , _) x⊑y = ∃⊑→⨆⊑⨆ inc
  where
  inc : ∀ m → ∃ λ n → Maybe→⊥ (f m) I.⊑ Maybe→⊥ (g n)
  inc m with inspect (f m)
  inc m | nothing , fm↑  = 0 , (Maybe→⊥ (f m)  ⊑⟨ cong Maybe→⊥ fm↑ ⟩≡
                                never          ⊑⟨ never⊑ _ ⟩■
                                Maybe→⊥ (g 0)  ■)
  inc m | just z  , fm↓z =
    k , (Maybe→⊥ (f m)     ⊑⟨ cong Maybe→⊥ fm↓z ⟩≡
         Maybe→⊥ (just z)  ⊑⟨ cong Maybe→⊥ (sym $ proj₂ y⇓z) ⟩≡
         Maybe→⊥ (g k)     ■)
    where
    y⇓z =        $⟨ ∣ m , fm↓z ∣ ⟩
      x A.∥⇓∥ z  ↝⟨ x⊑y z ⟩
      y A.∥⇓∥ z  ↝⟨ _⇔_.from (A.⇓⇔∥⇓∥ A-set y) ⟩□
      y A.⇓ z    □

    k : ℕ
    k = proj₁ y⇓z

-- Delay→⊥ maps weakly bisimilar values to equal values (if A is a
-- set).

Delay→⊥-≈→≡ : Is-set A → ∀ x y → x A.≈ y → Delay→⊥ x ≡ Delay→⊥ y
Delay→⊥-≈→≡ A-set x y =
  x A.≈ y                                            ↝⟨ Σ-map (Delay→⊥-mono A-set x y) (Delay→⊥-mono A-set y x) ⟩
  Delay→⊥ x I.⊑ Delay→⊥ y × Delay→⊥ x I.⊒ Delay→⊥ y  ↝⟨ uncurry antisymmetry ⟩□
  Delay→⊥ x ≡ Delay→⊥ y                              □

-- If A is a set, then values in A CA.⊥ can be mapped to values in the
-- inductive partiality monad.

⊥→⊥ : Is-set A → A CA.⊥ → A I.⊥
⊥→⊥ A-set =
  Quotient.rec Delay→⊥ (λ {x y} → Delay→⊥-≈→≡ A-set x y) ⊥-is-set

------------------------------------------------------------------------
-- A lemma

-- I._⇓_ and A._⇓_ are pointwise logically equivalent (via Delay→⊥),
-- for sets, assuming propositional extensionality.

⇓⇔⇓ :
  Is-set A → Propositional-extensionality a →
  ∀ x {y} → Delay→⊥ x I.⇓ y ⇔ x A.⇓ y
⇓⇔⇓ A-set prop-ext x@(f , _) {y} =
  Delay→⊥ x I.⇓ y                    ↝⟨ F.id ⟩
  ⨆ (Delay→Inc-seq x) I.⇓ y          ↔⟨ ⨆⇓≃∥∃⇓∥ prop-ext ⟩
  ∥ (∃ λ n → Maybe→⊥ (f n) I.⇓ y) ∥  ↝⟨ ∥∥-cong-⇔ (∃-cong λ _ → record { to = to _; from = cong Maybe→⊥ }) ⟩
  ∥ (∃ λ n → f n ↓ y) ∥              ↝⟨ F.id ⟩
  x A.∥⇓∥ y                          ↝⟨ inverse (A.⇓⇔∥⇓∥ A-set x) ⟩□
  x A.⇓ y                            □
  where
  to : ∀ n → Maybe→⊥ (f n) I.⇓ y → f n ↓ y
  to n f⇓y with f n
  ... | nothing = ⊥-elim $ now≢never prop-ext _ (sym f⇓y)
  ... | just y′ =
    just y′  ≡⟨ cong just y′≡y ⟩∎
    just y   ∎
    where
    y′≡y =            $⟨ f⇓y ⟩
      now y′ ≡ now y  ↔⟨ now≡now≃∥≡∥ prop-ext ⟩
      ∥ y′ ≡ y ∥      ↝⟨ ∥∥↔ (A-set _ _) ⟩□
      y′ ≡ y          □

------------------------------------------------------------------------
-- ⊥→⊥ is injective

-- Delay→⊥ is (kind of) injective (if A is a set, assuming
-- propositional extensionality).

Delay→⊥-injective :
  Is-set A → Propositional-extensionality a →
  ∀ x y → Delay→⊥ x ≡ Delay→⊥ y → x A.≈ y
Delay→⊥-injective A-set prop-ext x y x≡y =
    lemma A-set prop-ext x y (≡→⊑      x≡y)
  , lemma A-set prop-ext y x (≡→⊑ (sym x≡y))
  where
  ≡→⊑ : ∀ {x y} → x ≡ y → x I.⊑ y
  ≡→⊑ refl = ⊑-refl _

  lemma :
    Is-set A → Propositional-extensionality a →
    ∀ x y → Delay→⊥ x I.⊑ Delay→⊥ y → x A.∥⊑∥ y
  lemma A-set prop-ext x y x⊑y z =
    x A.∥⇓∥ z            ↝⟨ _⇔_.from (A.⇓⇔∥⇓∥ A-set x) ⟩
    x A.⇓ z              ↝⟨ _⇔_.from (⇓⇔⇓ A-set prop-ext x) ⟩
    Delay→⊥ x I.⇓ z      ↔⟨ ⇓≃now⊑ prop-ext ⟩
    now z I.⊑ Delay→⊥ x  ↝⟨ flip ⊑-trans x⊑y ⟩
    now z I.⊑ Delay→⊥ y  ↔⟨ inverse (⇓≃now⊑ prop-ext) ⟩
    Delay→⊥ y I.⇓ z      ↝⟨ _⇔_.to (⇓⇔⇓ A-set prop-ext y) ⟩
    y A.⇓ z              ↝⟨ _⇔_.to (A.⇓⇔∥⇓∥ A-set y) ⟩□
    y A.∥⇓∥ z            □

-- ⊥→⊥ A-set is injective (assuming propositional extensionality).

⊥→⊥-injective :
  (A-set : Is-set A) → Propositional-extensionality a →
  Injective (⊥→⊥ A-set)
⊥→⊥-injective A-set prop-ext {x} {y} =
  Quotient.elim-Prop
    (λ x → ⊥→⊥ A-set x ≡ ⊥→⊥ A-set y → x ≡ y)
    (λ x → Quotient.elim-Prop
       (λ y → Delay→⊥ x ≡ ⊥→⊥ A-set y → Quotient.[ x ] ≡ y)
       (λ y → []-respects-relation ∘
              Delay→⊥-injective A-set prop-ext x y)
       (λ _ → Π-closure ext 1 λ _ →
              /-is-set _ _)
       y)
    (λ _ → Π-closure ext 1 λ _ →
           /-is-set _ _)
    x

------------------------------------------------------------------------
-- ⊥→⊥ is surjective

-- Delay→⊥ is surjective (if A is a set, assuming propositional
-- extensionality and countable choice).

Delay→⊥-surjective :
  Is-set A →
  Propositional-extensionality a →
  Axiom-of-countable-choice a →
  Surjective Delay→⊥
Delay→⊥-surjective A-set prop-ext cc =
  ⊥-rec-⊥ (record
    { pe = constant-sequence nothing
    ; po = constant-sequence ∘ just
    ; pl = λ s →
             (∀ n → ∥ (∃ λ x → Delay→⊥ x ≡ s [ n ]) ∥)    ↝⟨ cc ⟩
             ∥ (∀ n → ∃ λ x → Delay→⊥ x ≡ s [ n ]) ∥      ↔⟨ ∥∥-cong ΠΣ-comm ⟩
             ∥ (∃ λ f → ∀ n → Delay→⊥ (f n) ≡ s [ n ]) ∥  ↝⟨ ∥∥-map (uncurry $ flip construct s) ⟩□
             ∥ (∃ λ x → Delay→⊥ x ≡ ⨆ s) ∥                □
    ; pp = λ _ → truncation-is-proposition
    })
  where
  -- The increasing sequences (of type A.Delay A) returned by this
  -- function are constant.

  constant-sequence : ∀ x → ∥ (∃ λ y → Delay→⊥ y ≡ Maybe→⊥ x) ∥
  constant-sequence x = ∣ (const x , const (inj₁ refl)) , ⨆-const ∣

  -- Given a sequence and an increasing sequence s that are pointwise
  -- equal (via Delay→⊥) one can construct an increasing sequence that
  -- is equal (via Delay→⊥) to ⨆ s.

  construct :
    (f : ℕ → A.Delay A)
    (s : I.Increasing-sequence A) →
    (∀ n → Delay→⊥ (f n) ≡ s [ n ]) →
    ∃ λ x → Delay→⊥ x ≡ ⨆ s
  construct f s h = x , x-correct
    where
    -- We use f and an isomorphism between ℕ and ℕ × ℕ to construct a
    -- function from ℕ to Maybe A.

    f₂ : ℕ → ℕ → Maybe A
    f₂ m n = proj₁ (f m) n

    f₁ : ℕ → Maybe A
    f₁ =
      ℕ        ↔⟨ ℕ↔ℕ² ⟩
      ℕ × ℕ    ↝⟨ uncurry f₂ ⟩□
      Maybe A  □

    -- All values that this function can terminate with are equal.

    termination-value-unique-f₂ :
      ∀ {m n y m′ n′ y′} →
      f₂ m n ↓ y × f₂ m′ n′ ↓ y′ →
      y ≡ y′
    termination-value-unique-f₂ {m} {n} {y} {m′} {n′} {y′} =
      f₂ m n ↓ y × f₂ m′ n′ ↓ y′  ↝⟨ f₂↓→⨆s⇓ ×-cong f₂↓→⨆s⇓ ⟩
      ⨆ s I.⇓ y × ⨆ s I.⇓ y′      ↝⟨ uncurry (termination-value-merely-unique prop-ext) ⟩
      ∥ y ≡ y′ ∥                  ↔⟨ ∥∥↔ (A-set _ _) ⟩□
      y ≡ y′                      □
      where
      f₂↓→⨆s⇓ : ∀ {y m n} → f₂ m n ↓ y → ⨆ s I.⇓ y
      f₂↓→⨆s⇓ {y} {m} f₂↓ =
        terminating-element-is-⨆ prop-ext s
          (s [ m ]        ≡⟨ sym (h m) ⟩
           Delay→⊥ (f m)  ≡⟨ _⇔_.from (⇓⇔⇓ A-set prop-ext (f m)) (_ , f₂↓) ⟩∎
           now y          ∎)

    termination-value-unique-f₁ :
      ∀ {y y′} →
      (∃ λ n → f₁ n ↓ y) →
      (∃ λ n → f₁ n ↓ y′) →
      y ≡ y′
    termination-value-unique-f₁ (_ , ↓y) (_ , ↓y′) =
      termination-value-unique-f₂ (↓y , ↓y′)

    abstract

      -- Thus the function can be completed to an increasing sequence.

      completed-f₁ : ∃ λ x → ∀ {y} → x A.⇓ y ⇔ ∃ λ n → f₁ n ↓ y
      completed-f₁ = A.complete-function f₁ termination-value-unique-f₁

    -- The increasing sequence that is returned above.

    x : A.Delay A
    x = proj₁ completed-f₁

    -- Every potential value in the increasing sequence x is smaller
    -- than or equal to (via Maybe→⊥) some value in s.

    x⊑s : ∀ m → ∃ λ n → Maybe→⊥ (proj₁ x m) I.⊑ s [ n ]
    x⊑s m with inspect (proj₁ x m)
    x⊑s m | nothing , x↑ =
        zero
      , (Maybe→⊥ (proj₁ x m)  ⊑⟨ cong Maybe→⊥ x↑ ⟩≡
         never                ⊑⟨ never⊑ _ ⟩■
         s [ 0 ]              ■)
    x⊑s m | just y , x↓ =
        n₁
      , (Maybe→⊥ (proj₁ x m)  ⊑⟨ cong Maybe→⊥ x↓ ⟩≡
         now y                ⊑⟨ sym f⇓ ⟩≡
         Delay→⊥ (f n₁)       ⊑⟨ h n₁ ⟩≡
         s [ n₁ ]             ■)
      where
      f₁↓ : ∃ λ n → f₁ n ↓ y
      f₁↓ = _⇔_.to (proj₂ completed-f₁) (_ , x↓)

      n  = proj₁ f₁↓
      n₁ = proj₁ (_↔_.to ℕ↔ℕ² n)
      n₂ = proj₂ (_↔_.to ℕ↔ℕ² n)

      f⇓ : Delay→⊥ (f n₁) I.⇓ y
      f⇓ =
        _≃_.from (⇓≃now⊑ prop-ext)
          (now y                        ⊑⟨ cong Maybe→⊥ $ sym $ proj₂ f₁↓ ⟩≡
           Maybe→⊥ (f₁ n)               ⊑⟨⟩
           Maybe→⊥ (f₂ n₁ n₂)           ⊑⟨⟩
           Maybe→⊥ (proj₁ (f n₁) n₂)    ⊑⟨⟩
           Delay→Inc-seq (f n₁) [ n₂ ]  ⊑⟨ upper-bound (Delay→Inc-seq (f n₁)) _ ⟩■
           Delay→⊥ (f n₁)               ■)

    -- Furthermore every potential value in f₂ is (in a certain sense)
    -- smaller than or equal to x.

    f₂⊑x : ∀ m n → Maybe→⊥ (f₂ m n) I.⊑ Delay→⊥ x
    f₂⊑x m n with inspect (f₂ m n)
    f₂⊑x m n | nothing , f₂↑ =
      Maybe→⊥ (f₂ m n)  ⊑⟨ cong Maybe→⊥ f₂↑ ⟩≡
      never             ⊑⟨ never⊑ _ ⟩■
      Delay→⊥ x         ■
    f₂⊑x m n | just y , f₂↓ =
      Maybe→⊥ (f₂ m n)  ⊑⟨ cong Maybe→⊥ f₂↓ ⟩≡
      now y             ⊑⟨ sym (_⇔_.from (⇓⇔⇓ A-set prop-ext x) x⇓) ⟩≡
      Delay→⊥ x         ■
      where
      k = _↔_.from ℕ↔ℕ² (m , n)

      f₁↓ : f₁ k ↓ y
      f₁↓ =
        f₁ k                        ≡⟨⟩
        uncurry f₂ (_↔_.to ℕ↔ℕ² k)  ≡⟨ cong (uncurry f₂) (_↔_.right-inverse-of ℕ↔ℕ² (m , n)) ⟩
        f₂ m n                      ≡⟨ f₂↓ ⟩∎
        just y                      ∎

      x⇓ : x A.⇓ y
      x⇓ = _⇔_.from (proj₂ completed-f₁) (k , f₁↓)

    -- Thus x is correctly defined.

    x-correct : Delay→⊥ x ≡ ⨆ s
    x-correct = antisymmetry
      (⊑→⨆⊑⨆ λ n →
         Delay→Inc-seq x [ n ]  ⊑⟨ proj₂ (x⊑s n) ⟩■
         s [ proj₁ (x⊑s n) ]    ■)
      (least-upper-bound _ _ λ m →
         s [ m ]                  ⊑⟨ sym (h m) ⟩≡
         Delay→⊥ (f m)            ⊑⟨⟩
         ⨆ (Delay→Inc-seq (f m))  ⊑⟨ least-upper-bound _ _ (f₂⊑x m) ⟩■
         Delay→⊥ x                ■)

-- ⊥→⊥ A-set is surjective (assuming propositional extensionality and
-- countable choice).

⊥→⊥-surjective :
  (A-set : Is-set A) →
  Propositional-extensionality a →
  Axiom-of-countable-choice a →
  Surjective (⊥→⊥ A-set)
⊥→⊥-surjective A-set prop-ext cc x =
  ∥∥-map (λ { (pre , can-pre≡x) → Quotient.[ pre ] , can-pre≡x })
         (Delay→⊥-surjective A-set prop-ext cc x)

------------------------------------------------------------------------
-- ⊥→⊥ is an equivalence

-- ⊥→⊥ A-set is an equivalence (assuming propositional extensionality
-- and countable choice).

⊥→⊥-equiv :
  (A-set : Is-set A) →
  Propositional-extensionality a →
  Axiom-of-countable-choice a →
  Is-equivalence (⊥→⊥ A-set)
⊥→⊥-equiv A-set prop-ext cc =                        $⟨ _,_ {B = const _}
                                                            (⊥→⊥-surjective A-set prop-ext cc)
                                                            (λ {_ _} → ⊥→⊥-injective A-set prop-ext) ⟩
  Surjective (⊥→⊥ A-set) × Injective (⊥→⊥ A-set)     ↝⟨ Σ-map id (_≃_.to (Injective≃Is-embedding ext /-is-set ⊥-is-set _)) ⟩
  Surjective (⊥→⊥ A-set) × Is-embedding (⊥→⊥ A-set)  ↝⟨ _≃_.to surjective×embedding≃equivalence ⟩□
  Is-equivalence (⊥→⊥ A-set)                         □

-- Thus the inductive definition of the partiality monad is equivalent
-- to the definition in Partiality-monad.Coinductive.Alternative, for
-- sets, assuming propositional extensionality and countable choice.

⊥≃⊥′ :
  Is-set A →
  Propositional-extensionality a →
  Axiom-of-countable-choice a →
  A CA.⊥ ≃ A I.⊥
⊥≃⊥′ A-set prop-ext choice = Eq.⟨ _ , ⊥→⊥-equiv A-set prop-ext choice ⟩

------------------------------------------------------------------------
-- The two definitions of the partiality monad are equivalent

-- The inductive and coinductive definitions of the partiality monad
-- are pointwise equivalent, for sets, assuming extensionality,
-- propositional extensionality and countable choice.

⊥≃⊥ :
  Is-set A →
  S.Extensionality a →
  Propositional-extensionality a →
  Axiom-of-countable-choice a →
  A I.⊥ ≃ A C.⊥
⊥≃⊥ A-set delay-ext prop-ext choice =
  A I.⊥   ↝⟨ inverse (⊥≃⊥′ A-set prop-ext choice) ⟩
  A CA.⊥  ↔⟨ CA.⊥↔⊥ A-set delay-ext ⟩□
  A C.⊥   □

-- The previous result has a number of preconditions. None of these
-- preconditions are needed to translate from the delay monad to the
-- higher inductive partiality monad.

Delay→⊥′ : D.Delay A ∞ → A I.⊥
Delay→⊥′ =
  D.Delay A ∞  ↝⟨ _⇔_.from A.Delay⇔Delay ⟩
  A.Delay A    ↝⟨ Delay→⊥ ⟩□
  A I.⊥        □

-- This translation turns weakly bisimilar computations into equal
-- computations, assuming that the underlying type is a set.

Delay→⊥′-≈→≡ :
  Is-set A →
  ∀ {x y} → x W.≈ y → Delay→⊥′ x ≡ Delay→⊥′ y
Delay→⊥′-≈→≡ A-set {x} {y} =
  x W.≈ y                                                ↝⟨ _⇔_.to (A.≈⇔≈′ A-set) ⟩
  _⇔_.from A.Delay⇔Delay x A.≈ _⇔_.from A.Delay⇔Delay y  ↝⟨ Delay→⊥-≈→≡ A-set (_⇔_.from A.Delay⇔Delay x) (_⇔_.from A.Delay⇔Delay y) ⟩□
  Delay→⊥′ x ≡ Delay→⊥′ y                                □

-- One can also translate from the coinductive to the inductive
-- partiality monad, as long as the underlying type is a set.

⊥→⊥′ : Is-set A → A C.⊥ → A I.⊥
⊥→⊥′ A-set = Quotient.rec
  Delay→⊥′
  (Trunc.rec (I.⊥-is-set _ _) (Delay→⊥′-≈→≡ A-set))
  I.⊥-is-set
