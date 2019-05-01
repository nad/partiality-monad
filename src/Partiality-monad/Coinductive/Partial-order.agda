------------------------------------------------------------------------
-- A partial order
------------------------------------------------------------------------

{-# OPTIONS --cubical #-}

open import Equality.Propositional
open import Univalence-axiom equality-with-J

module Partiality-monad.Coinductive.Partial-order
  {a} (prop-ext : Propositional-extensionality a) {A : Set a} where

open import Logical-equivalence using (_⇔_)
open import Prelude hiding (⊥; module W)
open import Size

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms equality-with-J using (ext)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-J as Trunc
open import Quotient.HIT equality-with-J as Quotient

open import Delay-monad
open import Delay-monad.Bisimilarity as B using (_≈_)
import Delay-monad.Partial-order as PO

open import Partiality-monad.Coinductive

-- An ordering relation.

LE : A ⊥ → A ⊥ → Proposition a
LE x y = Quotient.rec
  (λ x → LE″ x y)
  (left-lemma″-∥∥ y)
  is-set
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
    right-lemma-∥∥ = Trunc.rec (is-set _ _) right-lemma

  LE″ : Delay A ∞ → A ⊥ → Proposition a
  LE″ x y = Quotient.rec (LE′ x) right-lemma-∥∥ is-set y

  abstract

    left-lemma : ∀ {x y z} → x ≈ y → LE′ x z ≡ LE′ y z
    left-lemma x≈y =
      _↔_.to (⇔↔≡″ ext prop-ext)
             (record { to   = ∥∥-map (PO.transitive-≈⊑
                                        (B.symmetric x≈y))
                     ; from = ∥∥-map (PO.transitive-≈⊑ x≈y)
                     })

    left-lemma″ : ∀ {x y} z → x ≈ y → LE″ x z ≡ LE″ y z
    left-lemma″ {x} {y} z x≈y = Quotient.elim-Prop
      (λ z → LE″ x z ≡ LE″ y z)
      (λ _ → left-lemma x≈y)
      (λ _ → Is-set-∃-Is-proposition ext prop-ext _ _)
      z

    left-lemma″-∥∥ : ∀ {x y} z → ∥ x ≈ y ∥ → LE″ x z ≡ LE″ y z
    left-lemma″-∥∥ z = Trunc.rec
     (is-set _ _)
     (left-lemma″ z)

infix 4 _⊑_

_⊑_ : A ⊥ → A ⊥ → Set a
x ⊑ y = proj₁ (LE x y)

-- _⊑_ is propositional.

⊑-propositional : ∀ x y → Is-proposition (x ⊑ y)
⊑-propositional x y = proj₂ (LE x y)

-- _⊑_ is reflexive.

reflexive : ∀ x → x ⊑ x
reflexive = Quotient.elim-Prop
  _
  (λ x → ∣ PO.reflexive x ∣)
  (λ x → ⊑-propositional [ x ] [ x ])

-- _⊑_ is antisymmetric.

antisymmetric : ∀ x y → x ⊑ y → y ⊑ x → x ≡ y
antisymmetric = Quotient.elim-Prop
  (λ x → ∀ y → x ⊑ y → y ⊑ x → x ≡ y)
  (λ x → Quotient.elim-Prop
     (λ y → [ x ] ⊑ y → y ⊑ [ x ] → [ x ] ≡ y)
     (λ y ∥x⊑y∥ ∥y⊑x∥ →
        []-respects-relation $
        Trunc.rec truncation-is-proposition
          (λ x⊑y → ∥∥-map (PO.antisymmetric x⊑y) ∥y⊑x∥)
          ∥x⊑y∥)
     (λ _ → Π-closure ext 1 λ _ →
            Π-closure ext 1 λ _ →
            ⊥-is-set _ _))
  (λ _ → Π-closure ext 1 λ _ →
         Π-closure ext 1 λ _ →
         Π-closure ext 1 λ _ →
         ⊥-is-set _ _)

-- _⊑_ is transitive.

transitive : ∀ x y z → x ⊑ y → y ⊑ z → x ⊑ z
transitive = Quotient.elim-Prop
  (λ x → ∀ y z → x ⊑ y → y ⊑ z → x ⊑ z)
  (λ x → Quotient.elim-Prop
    (λ y → ∀ z → [ x ] ⊑ y → y ⊑ z → [ x ] ⊑ z)
    (λ y → Quotient.elim-Prop
       (λ z → ∥ x PO.⊑ y ∥ → [ y ] ⊑ z → [ x ] ⊑ z)
       (λ z ∥x⊑y∥ →
          Trunc.rec truncation-is-proposition
            (λ y⊑z → ∥∥-map (λ x⊑y → PO.transitive x⊑y y⊑z) ∥x⊑y∥))
       (λ _ → Π-closure ext 1 λ _ →
              Π-closure ext 1 λ _ →
              ⊑-propositional [ _ ] [ _ ]))
    (λ _ → Π-closure ext 1 λ z →
           Π-closure ext 1 λ _ →
           Π-closure ext 1 λ _ →
           ⊑-propositional [ _ ] z))
  (λ _ → Π-closure ext 1 λ _ →
         Π-closure ext 1 λ z →
         Π-closure ext 1 λ _ →
         Π-closure ext 1 λ _ →
         ⊑-propositional [ _ ] z)
