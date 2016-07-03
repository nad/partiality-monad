------------------------------------------------------------------------
-- A partial order
------------------------------------------------------------------------

{-# OPTIONS --without-K --rewriting #-}

open import Equality.Propositional
open import Univalence-axiom equality-with-J

module Partiality-monad.Coinductive.Partial-order
  {a} (univ : Univalence a) {A : Set a} where

open import H-level.Truncation.Propositional as Trunc
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (⊥; module W)
open import Quotient.HIT as Quotient

open import Bijection equality-with-J using (_↔_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J

open import Delay-monad
import Delay-monad.Partial-order as PO
open import Delay-monad.Weak-bisimilarity as W using (_≈_)

open import Partiality-monad.Coinductive

-- An ordering relation.

LE : A ⊥ → A ⊥ → Proposition a
LE x y = Quotient.rec
  (λ x → LE″ x y)
  (Trunc.rec
     (∃-H-level-H-level-1+ ext univ 1 _ _)
     (lemma₃ y))
  (∃-H-level-H-level-1+ ext univ 1)
  x
  where
  LE′ : Delay A ∞ → Delay A ∞ → Proposition a
  LE′ x y = ∥ x PO.⊑ y ∥ , truncation-is-proposition

  lemma₁ : ∀ {x y z} → x ≈ y → LE′ z x ≡ LE′ z y
  lemma₁ x≈y =
    _↔_.to (⇔↔≡′ ext univ)
           (record { to   = ∥∥-map (flip PO.transitive-⊑≈ x≈y)
                   ; from = ∥∥-map (flip PO.transitive-⊑≈
                                      (W.symmetric x≈y))
                   })

  lemma₂ : ∀ {x y z} → x ≈ y → LE′ x z ≡ LE′ y z
  lemma₂ x≈y =
    _↔_.to (⇔↔≡′ ext univ)
           (record { to   = ∥∥-map (PO.transitive-≈⊑
                                      (W.symmetric x≈y))
                   ; from = ∥∥-map (PO.transitive-≈⊑ x≈y)
                   })

  LE″ : Delay A ∞ → A ⊥ → Proposition a
  LE″ x y = Quotient.rec
    (LE′ x)
    (Trunc.rec (∃-H-level-H-level-1+ ext univ 1 _ _) lemma₁)
    (∃-H-level-H-level-1+ ext univ 1)
    y

  lemma₃ : ∀ {x y} z → x ≈ y → LE″ x z ≡ LE″ y z
  lemma₃ {x} {y} z x≈y = Quotient.elim-Prop
    (λ z → LE″ x z ≡ LE″ y z)
    (λ _ → lemma₂ x≈y)
    (λ _ → ∃-H-level-H-level-1+ ext univ 1 _ _)
    z

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
