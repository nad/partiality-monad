------------------------------------------------------------------------
-- The partiality monads in Partiality-monad.Inductive and
-- Partiality-monad.Coinductive are pointwise equivalent, for sets,
-- assuming extensionality, univalence and countable choice
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Partiality-monad.Equivalence where

open import Equality.Propositional
open import H-level.Truncation.Propositional as Trunc
open import Logical-equivalence using (_⇔_)
open import Prelude
open import Quotient.HIT as Quotient

open import Bijection equality-with-J using (_↔_)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F
open import H-level equality-with-J
open import Univalence-axiom equality-with-J

import Delay-monad as D
import Delay-monad.Alternative as A
import Delay-monad.Strong-bisimilarity as Strong-bisimilarity
import Delay-monad.Weak-bisimilarity as W
import Partiality-monad.Coinductive as C
import Partiality-monad.Equivalence.Lemmas as L
import Partiality-monad.Inductive as I
import Partiality-monad.Inductive.Properties as IP

private

  -- A lemma showing that two relations corresponding to weak
  -- bisimilarity are logically equivalent for sets.

  ~⇔≈ :
    ∀ {a} {A : Set a}
    (A-set : Is-set A) →
    let module R = L.relation-on-Seq in
    ∀ x y → x R.~ y ⇔ x A.≈ y
  ~⇔≈ A-set x y =
    ∀-cong-⇔ (λ _ → →-cong-⇔ (inverse (E.↓⇔∥↓∥ A-set {fp = x}))
                             (inverse (E.↓⇔∥↓∥ A-set {fp = y})))
      ×-cong
    ∀-cong-⇔ (λ _ → →-cong-⇔ (inverse (E.↓⇔∥↓∥ A-set {fp = y}))
                             (inverse (E.↓⇔∥↓∥ A-set {fp = x})))
    where
    module E = L.evaluating-sequences

-- The two definitions of the partiality monad are pointwise
-- equivalent, for sets, assuming extensionality, univalence and
-- countable choice.

partiality≃partiality :
  ∀ {a} {A : Set a} →
  Is-set A →
  Strong-bisimilarity.Extensionality a →
  Univalence a →
  Axiom-of-countable-choice a →
  A I.⊥ ≃ A C.⊥
partiality≃partiality {A = A} A-set delay-ext univ choice =

  A I.⊥    ↝⟨ inverse Eq.⟨ _ , L.canonical'-equivalence.canonical'-equiv
                                 A-set univ choice ⟩ ⟩
  R.Seq/~  ↔⟨ D↔D /-cong lemma ⟩

  A C.⊥    □

  where
  module E = L.evaluating-sequences
  module R = L.relation-on-Seq

  D↔D = A.Delay↔Delay delay-ext

  lemma : (x y : A.Delay A) →
          x R.~ y ⇔ ∥ _↔_.to D↔D x W.≈ _↔_.to D↔D y ∥
  lemma x y =
    x R.~ y                            ↔⟨ inverse $ ∥∥↔ (R.~-is-prop x y) ⟩
    ∥ x R.~ y ∥                        ↝⟨ ∥∥-cong-⇔ (~⇔≈ A-set x y) ⟩
    ∥ x A.≈ y ∥                        ↝⟨ ∥∥-cong-⇔ A.≈⇔≈ ⟩□
    ∥ _↔_.to D↔D x W.≈ _↔_.to D↔D y ∥  □

-- The previous result has a number of preconditions. None of these
-- preconditions are needed to translate from the delay monad to the
-- higher inductive partiality monad.

delay→partiality :
  ∀ {a} {A : Set a} →
  D.Delay A ∞ → A I.⊥
delay→partiality {A = A} =
  D.Delay A ∞  ↝⟨ _⇔_.from A.Delay⇔Delay ⟩
  A.Delay A    ↝⟨ L.monotone-to-QIIT.canonical ⟩□
  A I.⊥        □

-- This translation turns weakly bisimilar computations into equal
-- computations, assuming that the underlying type is a set.

delay→partiality-≈→≡ :
  ∀ {a} {A : Set a}
  (A-set : Is-set A) {x y : D.Delay A ∞} →
  x W.≈ y → delay→partiality x ≡ delay→partiality y
delay→partiality-≈→≡ A-set {x} {y} =
  x W.≈ y                                                ↝⟨ _⇔_.to A.≈⇔≈′ ⟩
  _⇔_.from A.Delay⇔Delay x A.≈ _⇔_.from A.Delay⇔Delay y  ↝⟨ _⇔_.from (~⇔≈ A-set (_⇔_.from A.Delay⇔Delay x) (_⇔_.from A.Delay⇔Delay y)) ⟩
  _⇔_.from A.Delay⇔Delay x R.~ _⇔_.from A.Delay⇔Delay y  ↝⟨ L.monotone-to-QIIT.canonical-respects-~ A-set ⟩□
  delay→partiality x ≡ delay→partiality y                □
  where
  module R = L.relation-on-Seq

-- One can also translate from the coinductive to the inductive
-- partiality monad, as long as the underlying type is a set.

partiality→partiality :
  ∀ {a} {A : Set a} →
  Is-set A →
  A C.⊥ → A I.⊥
partiality→partiality {A = A} A-set = Quotient.rec
  delay→partiality
  (Trunc.rec (IP.⊥-is-set _ _) (delay→partiality-≈→≡ A-set))
  IP.⊥-is-set
