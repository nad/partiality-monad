------------------------------------------------------------------------
-- Information orderings
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad.Alternative.Partial-order {a} {A : Set a} where

open import Equality.Propositional
open import H-level.Truncation.Propositional
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (module W)

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J

open import Delay-monad.Alternative
open import Delay-monad.Alternative.Equivalence
open import Delay-monad.Alternative.Termination
import Delay-monad.Partial-order as PO
import Delay-monad.Weak-bisimilarity as W

infix 4 _⊑_

-- Information orderings.

_⊑_ : Delay A → Delay A → Set a
x ⊑ y = ∀ z → x ⇓ z → y ⇓ z

_∥⊑∥_ : Delay A → Delay A → Set a
x ∥⊑∥ y = ∀ z → x ∥⇓∥ z → y ∥⇓∥ z

-- The two ordering relations are logically equivalent (if A is a
-- set).

⊑⇔∥⊑∥ : Is-set A → ∀ x y → x ⊑ y ⇔ x ∥⊑∥ y
⊑⇔∥⊑∥ A-set x y =
  ∀-cong-⇔ λ _ → →-cong-⇔ (⇓⇔∥⇓∥ A-set x) (⇓⇔∥⇓∥ A-set y)

-- The ordering relation _⊑_ is pointwise logically equivalent (via
-- Delay⇔Delay) to the ordering relation defined in
-- Delay-monad.Partial-order.

⊑⇔⊑ : ∀ x y →
      x ⊑ y ⇔ _⇔_.to Delay⇔Delay x PO.⊑ _⇔_.to Delay⇔Delay y
⊑⇔⊑ x y =
  x ⊑ y                                                              ↝⟨ F.id ⟩
  (∀ z → x ⇓ z → y ⇓ z)                                              ↝⟨ ∀-cong-⇔ (λ _ → →-cong-⇔ (⇓⇔⇓ x) (⇓⇔⇓ y)) ⟩
  (∀ z → _⇔_.to Delay⇔Delay x  W.⇓ z → _⇔_.to Delay⇔Delay y  W.⇓ z)  ↝⟨ inverse $ ∀-cong-⇔ (λ _ → →-cong-⇔ (_↔_.logical-equivalence PO.⇓↔⇓)
                                                                                                           (_↔_.logical-equivalence PO.⇓↔⇓)) ⟩
  (∀ z → _⇔_.to Delay⇔Delay x PO.⇓ z → _⇔_.to Delay⇔Delay y PO.⇓ z)  ↝⟨ inverse PO.⊑⇔⇓→⇓ ⟩□
  _⇔_.to Delay⇔Delay x PO.⊑ _⇔_.to Delay⇔Delay y                     □

⊑⇔⊑′ : ∀ {x y} →
       x PO.⊑ y ⇔ _⇔_.from Delay⇔Delay x ⊑ _⇔_.from Delay⇔Delay y
⊑⇔⊑′ {x} {y} =
  x PO.⊑ y                                                         ↝⟨ PO.⊑⇔⇓→⇓ ⟩
  (∀ z → x PO.⇓ z → y PO.⇓ z)                                      ↝⟨ ∀-cong-⇔ (λ _ → →-cong-⇔ (_↔_.logical-equivalence PO.⇓↔⇓)
                                                                                               (_↔_.logical-equivalence PO.⇓↔⇓))  ⟩
  (∀ z → x  W.⇓ z → y  W.⇓ z)                                      ↝⟨ ∀-cong-⇔ (λ _ → →-cong-⇔ ⇓⇔⇓′ ⇓⇔⇓′) ⟩
  (∀ z → _⇔_.from Delay⇔Delay x ⇓ z → _⇔_.from Delay⇔Delay y ⇓ z)  ↝⟨ F.id ⟩□
  _⇔_.from Delay⇔Delay x ⊑ _⇔_.from Delay⇔Delay y                  □

-- The ordering relation _∥⊑∥_ is pointwise propositional.

∥⊑∥-propositional : ∀ x y → Is-proposition (x ∥⊑∥ y)
∥⊑∥-propositional _ _ =
  Π-closure ext 1 λ _ →
  Π-closure ext 1 λ _ →
  truncation-is-proposition

-- The ordering relation _∥⊑∥_ is reflexive.

∥⊑∥-reflexive : ∀ x → x ∥⊑∥ x
∥⊑∥-reflexive _ = λ _ → id

-- The ordering relation _∥⊑∥_ is transitive.

∥⊑∥-transitive : ∀ x y z → x ∥⊑∥ y → y ∥⊑∥ z → x ∥⊑∥ z
∥⊑∥-transitive _ _ _ p q = λ z → q z ∘ p z
