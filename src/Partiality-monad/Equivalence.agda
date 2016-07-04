------------------------------------------------------------------------
-- The partiality monads in Partiality-monad.Inductive and
-- Partiality-monad.Coinductive are pointwise equivalent, for sets,
-- assuming extensionality, univalence and countable choice
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Partiality-monad.Equivalence where

open import Equality.Propositional
open import H-level.Truncation.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude
open import Quotient.HIT

open import Bijection equality-with-J using (_↔_)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F
open import H-level equality-with-J
open import Univalence-axiom equality-with-J

import Countchoice-equiv as L
import Delay-monad.Alternative as A
import Delay-monad.Strong-bisimilarity as Strong-bisimilarity
open import Delay-monad.Weak-bisimilarity using (_≈_)
import Partiality-monad.Coinductive as C
import Partiality-monad.Inductive as I

-- The two definitions of the partiality monad are pointwise
-- equivalent, for sets, assuming extensionality, univalence and
-- countable choice.

equivalent :
  ∀ {a} {A : Set a} →
  Is-set A →
  Strong-bisimilarity.Extensionality a →
  Univalence a →
  Axiom-of-countable-choice a →
  A I.⊥ ≃ A C.⊥
equivalent {A = A} A-set delay-ext univ choice =

  A I.⊥    ↝⟨ inverse Eq.⟨ _ , L.canonical'-equivalence.canonical'-equiv
                                 A-set univ choice ⟩ ⟩
  R.Seq/~  ↔⟨ D↔D /-cong lemma ⟩

  A C.⊥    □

  where
  module E = L.evaluating-sequences
  module R = L.relation-on-Seq

  D↔D = A.Delay↔Delay delay-ext

  lemma : (x y : A.Delay A) →
          x R.~ y ⇔ ∥ _↔_.to D↔D x ≈ _↔_.to D↔D y ∥
  lemma x y =
    x R.~ y                          ↔⟨ inverse $ ∥∥↔ (R.~-is-prop x y) ⟩
    ∥ x R.~ y ∥                      ↝⟨ ∥∥-cong-⇔ (∀-cong-⇔ (λ _ → →-cong-⇔ (inverse (E.↓⇔∥↓∥ A-set {fp = x}))
                                                                            (inverse (E.↓⇔∥↓∥ A-set {fp = y})))
                                                     ×-cong
                                                   ∀-cong-⇔ (λ _ → →-cong-⇔ (inverse (E.↓⇔∥↓∥ A-set {fp = y}))
                                                                            (inverse (E.↓⇔∥↓∥ A-set {fp = x})))) ⟩
    ∥ x A.≈ y ∥                      ↝⟨ ∥∥-cong-⇔ A.≈⇔≈ ⟩□
    ∥ _↔_.to D↔D x ≈ _↔_.to D↔D y ∥  □
