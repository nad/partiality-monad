------------------------------------------------------------------------
-- An alternative definition of the partiality monad: a variant of the
-- delay monad quotiented by a notion of weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --sized-types #-}

module Partiality-monad.Coinductive.Alternative where

open import Equality.Propositional.Cubical
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J hiding (⊥↔⊥)
open import H-level equality-with-J
open import H-level.Truncation.Propositional equality-with-paths
open import Quotient equality-with-paths

import Delay-monad.Alternative as A
import Delay-monad.Alternative.Equivalence as A
import Delay-monad.Alternative.Weak-bisimilarity as A
import Delay-monad.Bisimilarity as B
import Partiality-monad.Coinductive as C

-- The partiality monad, defined as the alternative definition of the
-- delay monad quotiented by weak bisimilarity.

_⊥ : ∀ {a} → Type a → Type a
A ⊥ = A.Delay A / A._≈_

-- The partiality monad is a set.

⊥-is-set : ∀ {a} {A : Type a} → Is-set (A ⊥)
⊥-is-set = /-is-set

-- This definition of the partiality monad is isomorphic to the one in
-- Partiality-monad.Coinductive, for sets, assuming extensionality.

⊥↔⊥ : ∀ {a} {A : Type a} →
      Is-set A →
      B.Extensionality a →
      A ⊥ ↔ A C.⊥
⊥↔⊥ {A = A} A-set delay-ext = D↔D /-cong lemma
  where
  D↔D = A.Delay↔Delay delay-ext

  lemma : (x y : A.Delay A) →
          x A.≈ y ⇔ ∥ _↔_.to D↔D x B.≈ _↔_.to D↔D y ∥
  lemma x y =
    x A.≈ y                            ↔⟨ inverse $ ∥∥↔ (A.≈-propositional x y) ⟩
    ∥ x A.≈ y ∥                        ↝⟨ ∥∥-cong-⇔ (A.≈⇔≈ A-set x y) ⟩□
    ∥ _↔_.to D↔D x B.≈ _↔_.to D↔D y ∥  □
