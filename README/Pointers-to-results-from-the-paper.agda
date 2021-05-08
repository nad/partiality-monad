------------------------------------------------------------------------
-- Pointers to results from the paper
------------------------------------------------------------------------

-- Note that this is a version of the code that does not quite match
-- the description in the paper. See README for some discussion of the
-- changes.

{-# OPTIONS --cubical --sized-types #-}

module README.Pointers-to-results-from-the-paper where

-- Library code.

import Delay-monad
import Delay-monad.Bisimilarity
import Delay-monad.Bisimilarity.Alternative
import Delay-monad.Monad
import Delay-monad.Partial-order
import Delay-monad.Termination
import Equality.Propositional as Equality
import Interval
import H-level.Truncation.Propositional as Truncation
import Quotient
import Univalence-axiom

-- Code from this development.

import Delay-monad.Alternative
import Delay-monad.Alternative.Equivalence
import Delay-monad.Alternative.Partial-order
import Delay-monad.Alternative.Termination
import Delay-monad.Alternative.Weak-bisimilarity
import Lifting
import Partiality-algebra
import Partiality-algebra.Category
import Partiality-algebra.Eliminators
import Partiality-algebra.Fixpoints
import Partiality-algebra.Pi
import Partiality-monad.Coinductive.Alternative
import Partiality-monad.Inductive as Partiality-monad
import Partiality-monad.Inductive.Alternative-order as Alternative-order
import Partiality-monad.Inductive.Eliminators
import Partiality-monad.Inductive.Fixpoints
import Partiality-monad.Inductive.Monad as Monad
import Partiality-monad.Inductive.Monad.Adjunction as Adjunction
import Partiality-monad.Equivalence
import README.Lambda
import Search

------------------------------------------------------------------------
-- Section 2

-- Note that most of the following definitions are taken from a
-- library.

-- Extensionality for functions.

Extensionality = Equality.Extensionality
ext            = Interval.ext

-- Strong bisimilarity implies equality for the delay monad.

Delay-ext = Delay-monad.Bisimilarity.Extensionality

-- The property of being a set.

Is-set = Equality.Is-set

-- The property of being a proposition.

Is-proposition = Equality.Is-proposition

-- Propositional extensionality.

Propositional-extensionality =
  Univalence-axiom.Propositional-extensionality

-- The univalence axiom.

Univalence = Univalence-axiom.Univalence

-- Quotient types.

import Quotient

-- Countable choice.

Countable-choice = Truncation.Axiom-of-countable-choice

------------------------------------------------------------------------
-- Section 3.1

-- Definition 1: Partiality algebras and partiality algebra morphisms.
-- The function η is called now and ⊥ is called never.

Partiality-algebra = Partiality-algebra.Partiality-algebra
Morphism           = Partiality-algebra.Morphism

-- An identity morphism.

id = Partiality-algebra.id

-- Composition of morphisms.

_∘_ = Partiality-algebra._∘_

-- Partiality algebras form a category.

category = Partiality-algebra.Category.category

-- The partiality monad, defined as a QIIT. (The proof α is called
-- antisymmetry.)

_⊥ = Partiality-monad._⊥

-- A partiality algebra for the partiality monad.

partiality-monad = Partiality-monad.partiality-algebra

-- Initiality.

Initial = Partiality-algebra.Eliminators.Initial

-- Theorem 2.

Induction-principle =
  Partiality-algebra.Eliminators.Elimination-principle
universality-to-induction =
  Partiality-algebra.Eliminators.∀initiality→∀eliminators
induction-to-universality =
  Partiality-algebra.Eliminators.∀eliminators→∀initiality

-- The partiality monad's induction principle.

induction-principle = Partiality-monad.eliminators

-- A proof that shows that A ⊥ is a set without making use of the
-- set-truncation "constructor".

T-is-set = Partiality-algebra.Partiality-algebra-with.T-is-set

-- Lemma 3.

lemma-3 = Partiality-monad.Inductive.Eliminators.⊥-rec-⊥

------------------------------------------------------------------------
-- Section 3.2

-- Definition 4: The category ω-CPO of pointed ω-cpos.

ω-CPO = Adjunction.ω-CPPO
ω-cpo = Adjunction.ω-cppo

-- The forgetful functor U from ω-CPO (and in fact Part_A for any A)
-- to SET.

U = Adjunction.Forget

-- The functor F from SET to ω-CPO.

F = Adjunction.Partial

-- Theorem 5.

theorem-5 = Adjunction.Partial⊣Forget

-- Corollary 6.

corollary-6 = Adjunction.Partiality-monad

-- A direct construction of a monad structure on _⊥.

μ                 = Monad.join
module Monad-laws = Monad.Monad-laws

------------------------------------------------------------------------
-- Section 3.3

-- Lemma 7. For the second part the code uses a propositional
-- truncation that is not present in the paper: the result proved in
-- the code is more general, and works even if the type "A" is not a
-- set.

lemma-7-part-1 = Alternative-order.now⊑never≃⊥
lemma-7-part-2 = Alternative-order.now⊑now≃∥≡∥
lemma-7-part-3 = Alternative-order.now⊑⨆≃∥∃now⊑∥

-- Corollary 8. For the second part the code uses a propositional
-- truncation that is not present in the paper: the result proved in
-- the code is more general, and works even if the type "A" is not a
-- set.

corollary-8-part-1 = Alternative-order.now⊑→⇓
corollary-8-part-2 = Alternative-order.now≡now≃∥≡∥
corollary-8-part-3 = Alternative-order.now≢never

-- The order is flat.

flat-order = Alternative-order.flat-order

------------------------------------------------------------------------
-- Section 4, not including Sections 4.1 and 4.2

-- Definition 9: The delay monad and weak bisimilarity. The definition
-- of _↓_ is superficially different from the one in the paper. The
-- first definition of weak bisimilarity, _∼D_, is different from the
-- one in the paper, but is logically equivalent to the second one,
-- _∼D′_, which is closer to the paper's definition.

Delay  = Delay-monad.Delay
_↓D_   = Delay-monad.Termination._⇓_
_∼D_   = Delay-monad.Bisimilarity._≈_
_∼D′_  = Delay-monad.Bisimilarity.Alternative._≈₂_
∼D⇔∼D′ = Delay-monad.Partial-order.≈⇔≈₂

-- The delay monad is a monad.

Delay-monad = Delay-monad.Monad.delay-monad

-- The relation _↓D_ is pointwise propositional (when the type "A" is
-- a set).

↓D-propositional = Delay-monad.Termination.Terminates-propositional

-- The relation _∼D′_ is pointwise propositional (when the type "A" is
-- a set).

∼D′-propositional =
  Delay-monad.Bisimilarity.Alternative.≈₂-propositional

-- _∼D_ is an equivalence relation.

∼D-reflexive  = Delay-monad.Bisimilarity.reflexive
∼D-symmetric  = Delay-monad.Bisimilarity.symmetric
∼D-transitive = Delay-monad.Bisimilarity.transitive-≈

------------------------------------------------------------------------
-- Section 4.1

-- The predicate is-mon.

is-mon = Delay-monad.Alternative.Increasing

-- Monotone sequences.

Seq = Delay-monad.Alternative.Delay

-- Lemma 10.

lemma-10 = Delay-monad.Alternative.Equivalence.Delay↔Delay

-- The relation ↓_Seq.

_↓-Seq_ = Delay-monad.Alternative.Termination._⇓_

-- This relation is pointwise logically equivalent to a
-- propositionally truncated variant (when the type "A" is a set).

↓-Seq⇔∥↓-Seq∥ = Delay-monad.Alternative.Termination.⇓⇔∥⇓∥

-- The relation ⊑_Seq.

_⊑-Seq_ = Delay-monad.Alternative.Partial-order._∥⊑∥_

-- This relation is pointwise propositional.

⊑-Seq-propositional =
  Delay-monad.Alternative.Partial-order.∥⊑∥-propositional

-- The relation ∼_Seq.

_∼-Seq_ = Delay-monad.Alternative.Weak-bisimilarity._≈_

-- This relation is pointwise propositional.

≈-Seq-propositional =
  Delay-monad.Alternative.Weak-bisimilarity.≈-propositional

-- Lemma 11.

lemma-11 = Partiality-monad.Coinductive.Alternative.⊥↔⊥

------------------------------------------------------------------------
-- Section 4.2

-- The function w.

w = Partiality-monad.Equivalence.Delay→⊥

-- Lemma 12.

w-monotone = Partiality-monad.Equivalence.Delay→⊥-mono
w̃          = Partiality-monad.Equivalence.⊥→⊥

-- Lemma 13.

lemma-13 = Partiality-monad.Equivalence.⊥→⊥-injective

-- Lemma 14.

lemma-14 = Partiality-monad.Equivalence.Delay→⊥-surjective

-- The function w̃ is surjective.

w̃-surjective = Partiality-monad.Equivalence.⊥→⊥-surjective

-- Theorem 15.

theorem-15-part-1 = Partiality-monad.Equivalence.⊥→⊥-equiv
theorem-15-part-2 = Partiality-monad.Equivalence.⊥≃⊥′
theorem-15-part-3 = Partiality-monad.Equivalence.⊥≃⊥

------------------------------------------------------------------------
-- Section 5.1

-- A fixpoint combinator.

fix = Partiality-algebra.Fixpoints.fix

-- If the argument is ω-continuous, then the result is a least fixed
-- point.

fixed-point = Partiality-algebra.Fixpoints.fix-is-fixpoint-combinator
least       = Partiality-algebra.Fixpoints.fix-is-least

-- A kind of dependent function space with a type as the domain and a
-- family of partiality algebras as the codomain. The result is a
-- partiality algebra.

Π = Partiality-algebra.Pi.Π

-- The search function.

module The-search-function = Search.Direct

------------------------------------------------------------------------
-- Section 5.3

-- Operational semantics.

module Operational-semantics = README.Lambda

------------------------------------------------------------------------
-- Section 6

-- A quotient inductive-inductive definition of the lifting
-- construction on ω-cpos. (This construction is based on a suggestion
-- from Paolo Capriotti.)

module Lifting-construction = Lifting
