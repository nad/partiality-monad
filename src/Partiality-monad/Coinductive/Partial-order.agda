------------------------------------------------------------------------
-- A partial order
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe --sized-types #-}

module Partiality-monad.Coinductive.Partial-order {a} {A : Set a} where

open import Equality.Propositional.Cubical
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (⊥; module W)
open import Prelude.Size

open import Bijection equality-with-J using (_↔_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-paths
  as Trunc
open import Quotient equality-with-paths as Quotient
open import Univalence-axiom equality-with-J

open import Delay-monad
open import Delay-monad.Bisimilarity as B using (_≈_)
import Delay-monad.Partial-order as PO

open import Partiality-monad.Coinductive

-- An ordering relation.

LE : A ⊥ → A ⊥ → Proposition a
LE x y = Quotient.rec
  (λ where
     .[]ʳ x                 → LE″ x y
     .[]-respects-relationʳ → left-lemma″-∥∥ y
     .is-setʳ               → is-set)
  x
  where
  LE′ : Delay A ∞ → Delay A ∞ → Proposition a
  LE′ x y = ∥ x PO.⊑ y ∥ , truncation-is-proposition

  abstract

    is-set : Is-set (∃ Is-proposition)
    is-set = Is-set-∃-Is-proposition ext prop-ext

    right-lemma : ∀ {x y z} → x ≈ y → LE′ z x ≡ LE′ z y
    right-lemma x≈y =
      _↔_.to (⇔↔≡″ ext prop-ext)
             (record { to   = ∥∥-map (flip PO.transitive-⊑≈ x≈y)
                     ; from = ∥∥-map (flip PO.transitive-⊑≈
                                        (B.symmetric x≈y))
                     })

    right-lemma-∥∥ : ∀ {x y z} → ∥ x ≈ y ∥ → LE′ z x ≡ LE′ z y
    right-lemma-∥∥ = Trunc.rec is-set right-lemma

  LE″ : Delay A ∞ → A ⊥ → Proposition a
  LE″ x y = Quotient.rec
    (λ where
       .[]ʳ                   → LE′ x
       .[]-respects-relationʳ → right-lemma-∥∥
       .is-setʳ               → is-set)
    y

  abstract

    left-lemma : ∀ {x y z} → x ≈ y → LE′ x z ≡ LE′ y z
    left-lemma x≈y =
      _↔_.to (⇔↔≡″ ext prop-ext)
             (record { to   = ∥∥-map (PO.transitive-≈⊑
                                        (B.symmetric x≈y))
                     ; from = ∥∥-map (PO.transitive-≈⊑ x≈y)
                     })

    left-lemma″ : ∀ {x y} z → x ≈ y → LE″ x z ≡ LE″ y z
    left-lemma″ {x} {y} z x≈y = Quotient.elim-prop
      {P = λ z → LE″ x z ≡ LE″ y z}
      (λ where
         .[]ʳ _             → left-lemma x≈y
         .is-propositionʳ _ →
           Is-set-∃-Is-proposition ext prop-ext)
      z

    left-lemma″-∥∥ : ∀ {x y} z → ∥ x ≈ y ∥ → LE″ x z ≡ LE″ y z
    left-lemma″-∥∥ z = Trunc.rec
     is-set
     (left-lemma″ z)

infix 4 _⊑_

_⊑_ : A ⊥ → A ⊥ → Set a
x ⊑ y = proj₁ (LE x y)

-- _⊑_ is propositional.

⊑-propositional : ∀ x y → Is-proposition (x ⊑ y)
⊑-propositional x y = proj₂ (LE x y)

-- _⊑_ is reflexive.

reflexive : ∀ x → x ⊑ x
reflexive = Quotient.elim-prop λ where
  .[]ʳ x             → ∣ PO.reflexive x ∣
  .is-propositionʳ x → ⊑-propositional [ x ] [ x ]

-- _⊑_ is antisymmetric.

antisymmetric : ∀ x y → x ⊑ y → y ⊑ x → x ≡ y
antisymmetric = Quotient.elim-prop λ where
  .[]ʳ x → Quotient.elim-prop (λ where
    .[]ʳ y ∥x⊑y∥ ∥y⊑x∥ →
      []-respects-relation $
      Trunc.rec truncation-is-proposition
        (λ x⊑y → ∥∥-map (PO.antisymmetric x⊑y) ∥y⊑x∥)
        ∥x⊑y∥
    .is-propositionʳ _ →
      Π-closure ext 1 λ _ →
      Π-closure ext 1 λ _ →
      ⊥-is-set)
  .is-propositionʳ _ →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    ⊥-is-set

-- _⊑_ is transitive.

transitive : ∀ x y z → x ⊑ y → y ⊑ z → x ⊑ z
transitive = Quotient.elim-prop λ where
  .[]ʳ x → Quotient.elim-prop λ where
    .[]ʳ y → Quotient.elim-prop λ where
      .[]ʳ z ∥x⊑y∥ →
        Trunc.rec truncation-is-proposition
          (λ y⊑z → ∥∥-map (λ x⊑y → PO.transitive x⊑y y⊑z) ∥x⊑y∥)
      .is-propositionʳ _ →
        Π-closure ext 1 λ _ →
        Π-closure ext 1 λ _ →
        ⊑-propositional [ _ ] [ _ ]
    .is-propositionʳ _ →
      Π-closure ext 1 λ z →
      Π-closure ext 1 λ _ →
      Π-closure ext 1 λ _ →
      ⊑-propositional [ _ ] z
  .is-propositionʳ _ →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ z →
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    ⊑-propositional [ _ ] z
