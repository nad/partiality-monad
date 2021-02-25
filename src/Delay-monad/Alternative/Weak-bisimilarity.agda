------------------------------------------------------------------------
-- Weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe --sized-types #-}

open import Prelude hiding (module W)

module Delay-monad.Alternative.Weak-bisimilarity {a} {A : Type a} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)

open import Equivalence-relation equality-with-J
open import Function-universe equality-with-J
open import H-level equality-with-J
open import H-level.Closure equality-with-J

open import Delay-monad.Alternative
open import Delay-monad.Alternative.Equivalence
open import Delay-monad.Alternative.Partial-order
import Delay-monad.Bisimilarity as B
import Delay-monad.Partial-order as PO

infix 4 _≈_

-- Weak bisimilarity.

_≈_ : Delay A → Delay A → Type a
x ≈ y = x ∥⊑∥ y × y ∥⊑∥ x

-- Weak bisimilarity is pointwise propositional.

≈-propositional : ∀ x y → Is-proposition (x ≈ y)
≈-propositional x y =
  ×-closure 1 (∥⊑∥-propositional x y) (∥⊑∥-propositional y x)

-- Weak bisimilarity is an equivalence relation.

≈-is-equivalence-relation : Is-equivalence-relation _≈_
≈-is-equivalence-relation = record
  { reflexive  = λ {x} → ∥⊑∥-reflexive x , ∥⊑∥-reflexive x
  ; symmetric  = λ { (p , q) → q , p }
  ; transitive = λ {x y z} → Σ-zip (∥⊑∥-transitive x y z)
                                   (flip (∥⊑∥-transitive z y x))
  }

-- The notion of weak bisimilarity defined here is logically
-- equivalent (via Delay⇔Delay) to the one defined for the
-- coinductive delay monad (if A is a set).

≈⇔≈ :
  Is-set A →
  ∀ x y → x ≈ y ⇔ _⇔_.to Delay⇔Delay x B.≈ _⇔_.to Delay⇔Delay y
≈⇔≈ A-set x y =
  x ∥⊑∥ y × y ∥⊑∥ x                ↝⟨ inverse (⊑⇔∥⊑∥ A-set x y ×-cong ⊑⇔∥⊑∥ A-set y x) ⟩
  x ⊑ y × y ⊑ x                    ↝⟨ ⊑⇔⊑ x y ×-cong ⊑⇔⊑ y x ⟩
  to x PO.⊑ to y × to y PO.⊑ to x  ↝⟨ inverse PO.≈⇔⊑×⊒ ⟩□
  to x B.≈ to y                    □
  where
  open _⇔_ Delay⇔Delay

≈⇔≈′ :
  Is-set A →
  ∀ {x y} → x B.≈ y ⇔ _⇔_.from Delay⇔Delay x ≈ _⇔_.from Delay⇔Delay y
≈⇔≈′ A-set {x} {y} =
  x B.≈ y                                ↝⟨ PO.≈⇔⊑×⊒ ⟩
  x PO.⊑ y × y PO.⊑ x                    ↝⟨ ⊑⇔⊑′ ×-cong ⊑⇔⊑′ ⟩
  from x ⊑ from y × from y ⊑ from x      ↝⟨ ⊑⇔∥⊑∥ A-set (from x) (from y) ×-cong ⊑⇔∥⊑∥ A-set (from y) (from x) ⟩□
  from x ∥⊑∥ from y × from y ∥⊑∥ from x  □
  where
  open _⇔_ Delay⇔Delay
