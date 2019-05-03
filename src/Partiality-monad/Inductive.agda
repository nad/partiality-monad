------------------------------------------------------------------------
-- A quotient inductive-inductive definition of the partiality monad
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Partiality-monad.Inductive where

import Equality.Path as P
open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms equality-with-J
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J hiding (Type)
open import H-level.Closure equality-with-J

open import Partiality-algebra as PA hiding (_∘_)
open import Partiality-algebra.Eliminators as PAE hiding (Arguments)
import Partiality-algebra.Properties

private
  variable
    a ℓ p q : Level
    A       : Set a

mutual

  infix 10 _⊥
  infix 4  _⊑_

  -- Originally the monad was postulated. After the release of Cubical
  -- Agda it was turned into a QIIT, but in order to not get any extra
  -- computation rules it was made abstract.

  abstract

    -- The partiality monad.

    data _⊥ (A : Set a) : Set a where
      never        : A ⊥
      now          : A → A ⊥
      ⨆            : Increasing-sequence A → A ⊥
      antisymmetry : x ⊑ y → y ⊑ x → x P.≡ y

      -- We have chosen to explicitly make the type set-truncated.
      -- However, this constructor is mostly unused: it is used to
      -- define partiality-algebra below (and the corresponding record
      -- field is in turn also mostly unused, see its documentation
      -- for details), and it is mentioned in the implementation of
      -- eliminators (also below).
      UIP-unused : P.Uniqueness-of-identity-proofs (A ⊥)

  -- Increasing sequences.

  Increasing-sequence : Set ℓ → Set ℓ
  Increasing-sequence A =
    Σ (ℕ → A ⊥) λ f → ∀ n → f n ⊑ f (suc n)

  -- Upper bounds.

  Is-upper-bound :
    {A : Set a} → Increasing-sequence A → A ⊥ → Set a
  Is-upper-bound s x = ∀ n → (s [ n ]) ⊑ x

  -- A projection function for Increasing-sequence.

  infix 30 _[_]

  _[_] : Increasing-sequence A → ℕ → A ⊥
  _[_] s n = proj₁ {A = _ → _ ⊥} s n

  private
    variable
      x y z : A ⊥

  abstract

    -- An ordering relation.

    data _⊑_ {A : Set a} : A ⊥ → A ⊥ → Set a where
      ⊑-refl             : ∀ x → x ⊑ x
      ⊑-trans            : x ⊑ y → y ⊑ z → x ⊑ z
      never⊑             : ∀ x → never ⊑ x
      upper-bound        : ∀ s → Is-upper-bound s (⨆ s)
      least-upper-bound  : ∀ s ub → Is-upper-bound s ub → ⨆ s ⊑ ub
      ⊑-proof-irrelevant : P.Proof-irrelevant (x ⊑ y)

-- A partiality algebra for the partiality monad.

partiality-algebra : ∀ {a} (A : Set a) → Partiality-algebra a a A
partiality-algebra A = record
  { Type                    = A ⊥
  ; partiality-algebra-with = record
    { _⊑_                = _⊑_
    ; never              = never′
    ; now                = now′
    ; ⨆                  = ⨆′
    ; antisymmetry       = antisymmetry′
    ; Type-UIP-unused    = Type-UIP-unused′
    ; ⊑-refl             = ⊑-refl′
    ; ⊑-trans            = ⊑-trans′
    ; never⊑             = never⊑′
    ; upper-bound        = upper-bound′
    ; least-upper-bound  = least-upper-bound′
    ; ⊑-proof-irrelevant = ⊑-proof-irrelevant′
    }
  }
  where

  abstract

    never′ : A ⊥
    never′ = never

    now′ : A → A ⊥
    now′ = now

    ⨆′ : Increasing-sequence A → A ⊥
    ⨆′ = ⨆

    antisymmetry′ : x ⊑ y → y ⊑ x → x ≡ y
    antisymmetry′ = λ p q → _↔_.from ≡↔≡ (antisymmetry p q)

    Type-UIP-unused′ : Uniqueness-of-identity-proofs (A ⊥)
    Type-UIP-unused′ =                       $⟨ (λ {x y} → UIP-unused {x = x} {y = y}) ⟩
      P.Uniqueness-of-identity-proofs (A ⊥)  ↔⟨ inverse set↔UIP ⟩
      Is-set (A ⊥)                           ↝⟨ _⇔_.to set⇔UIP ⟩
      Uniqueness-of-identity-proofs (A ⊥)    □

    ⊑-refl′ : ∀ x → x ⊑ x
    ⊑-refl′ = ⊑-refl

    ⊑-trans′ : x ⊑ y → y ⊑ z → x ⊑ z
    ⊑-trans′ = ⊑-trans

    never⊑′ : ∀ x → never′ ⊑ x
    never⊑′ = never⊑

    upper-bound′ : ∀ s → Is-upper-bound s (⨆′ s)
    upper-bound′ = upper-bound

    least-upper-bound′ : ∀ s ub → Is-upper-bound s ub → ⨆′ s ⊑ ub
    least-upper-bound′ = least-upper-bound

    ⊑-proof-irrelevant′ : Proof-irrelevant (x ⊑ y)
    ⊑-proof-irrelevant′ {x = x} {y = y} =
                                  $⟨ ⊑-proof-irrelevant ⟩
      P.Proof-irrelevant (x ⊑ y)  ↔⟨ inverse propositional↔irrelevant ⟩
      Is-proposition (x ⊑ y)      ↝⟨ _⇔_.to propositional⇔irrelevant ⟩□
      Proof-irrelevant (x ⊑ y)    □

abstract

  -- The elimination principle.

  eliminators : Elimination-principle p q (partiality-algebra A)
  eliminators {A = A} args = record
    { ⊥-rec       = ⊥-rec
    ; ⊑-rec       = ⊑-rec
    ; ⊥-rec-never = refl
    ; ⊥-rec-now   = λ _ → refl
    ; ⊥-rec-⨆     = λ _ → refl
    }
    where
    module A = PAE.Arguments args

    mutual

      inc-rec : (s : Increasing-sequence A) → A.Inc A.P A.Q s
      inc-rec (s , inc) = (λ n → ⊥-rec (s   n))
                        , (λ n → ⊑-rec (inc n))

      ⊥-rec : (x : A ⊥) → A.P x
      ⊥-rec never                                = A.pe
      ⊥-rec (now x)                              = A.po x
      ⊥-rec (⨆ s)                                = A.pl s (inc-rec s)
      ⊥-rec (antisymmetry {x = x} {y = y} p q i) = subst≡→[]≡
                                                     (A.pa p q
                                                        (⊥-rec x) (⊥-rec y)
                                                        (⊑-rec p) (⊑-rec q))
                                                     i
      ⊥-rec (UIP-unused {x = x} {y = y} p q i j) = lemma i j
        where
        lemma :
          P.[ (λ i → P.[ (λ j → A.P (UIP-unused p q i j)) ]
                       ⊥-rec x ≡ ⊥-rec y) ]
            (λ i → ⊥-rec (p i)) ≡ (λ i → ⊥-rec (q i))
        lemma = P.heterogeneous-UIP
                  (λ x → _↔_.to (H-level↔H-level _)
                           (_⇔_.from set⇔UIP (A.pp {x = x})))
                  (UIP-unused p q)

      ⊑-rec : (x⊑y : x ⊑ y) → A.Q (⊥-rec x) (⊥-rec y) x⊑y
      ⊑-rec (⊑-refl x)                                 = A.qr x (⊥-rec x)
      ⊑-rec (⊑-trans {x = x} {y = y} {z = z} p q)      = A.qt p q
                                                           (⊥-rec x) (⊥-rec y) (⊥-rec z)
                                                           (⊑-rec p) (⊑-rec q)
      ⊑-rec (never⊑ x)                                 = A.qe x (⊥-rec x)
      ⊑-rec (upper-bound s n)                          = A.qu s (inc-rec s) n
      ⊑-rec (least-upper-bound s ub is-ub)             = A.ql s ub is-ub
                                                           (inc-rec s) (⊥-rec ub)
                                                           (λ n → ⊑-rec (is-ub n))
      ⊑-rec (⊑-proof-irrelevant {x = x} {y = y} p q i) = lemma i
        where
        lemma : P.[ (λ i → A.Q (⊥-rec x) (⊥-rec y)
                             (⊑-proof-irrelevant p q i)) ]
                  ⊑-rec p ≡ ⊑-rec q
        lemma =
          P.heterogeneous-irrelevance
            (λ p → _↔_.to (H-level↔H-level _)
                     (_⇔_.from propositional⇔irrelevant
                        (A.qp (⊥-rec x) (⊥-rec y) p)))

module _ {A : Set a} where

  open Partiality-algebra (partiality-algebra A) public
    hiding (Type; _⊑_; _[_]; Increasing-sequence; Is-upper-bound)
    renaming ( Type-is-set to ⊥-is-set
             ; equality-characterisation-Type to
               equality-characterisation-⊥
             )

  open Partiality-algebra.Properties (partiality-algebra A) public

-- The eliminators' arguments.

Arguments : ∀ {a} p q (A : Set a) → Set (a ⊔ lsuc (p ⊔ q))
Arguments p q A = PAE.Arguments p q (partiality-algebra A)

module _ (args : Arguments p q A) where
  open Eliminators (eliminators args) public

-- Initiality.

initial : Initial p q (partiality-algebra A)
initial = eliminators→initiality _ eliminators
