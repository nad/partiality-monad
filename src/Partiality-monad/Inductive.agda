------------------------------------------------------------------------
-- A higher inductive-inductive definition of the partiality monad
------------------------------------------------------------------------

-- Note that this module is experimental: it uses rewrite rules to
-- encode a higher inductive-inductive type.

{-# OPTIONS --without-K --rewriting #-}

module Partiality-monad.Inductive {a} where

open import Equality.Propositional
open import Prelude hiding (⊥)

-- The partiality monad (_⊥) and the information ordering (_⊑_) are
-- defined simultaneously.

infix 10 _⊥
infix  4 _⊑_ _⊒_

postulate
  _⊥  : Set a → Set a
  _⊑_ : {A : Set a} → A ⊥ → A ⊥ → Set a

_⊒_ : {A : Set a} → A ⊥ → A ⊥ → Set a
x ⊒ y = y ⊑ x

-- Increasing sequences.

Increasing-sequence : Set a → Set a
Increasing-sequence A = ∃ λ (f : ℕ → A ⊥) → ∀ n → f n ⊑ f (suc n)

module _ {A : Set a} where

  -- Projection functions for Increasing-sequence.

  infix 30 _[_]

  _[_] : Increasing-sequence A → ℕ → A ⊥
  s [ n ] = proj₁ s n

  increasing : (s : Increasing-sequence A) →
               ∀ n → s [ n ] ⊑ s [ suc n ]
  increasing = proj₂

  -- Upper bounds.

  Is-upper-bound : Increasing-sequence A → A ⊥ → Set a
  Is-upper-bound s x = ∀ n → s [ n ] ⊑ x

  postulate

    -- _⊥ "constructors".

    never        : A ⊥
    now          : A → A ⊥
    ⨆            : Increasing-sequence A → A ⊥
    antisymmetry : {x y : A ⊥} → x ⊑ y → x ⊒ y → x ≡ y

  private
    postulate

      -- We have chosen to explicitly make the type set-truncated.
      -- However, this "constructor" is private in order to highlight
      -- that it is not used anywhere in the development.
      ≡-proof-irrelevant : {x y : A ⊥} → Proof-irrelevant (x ≡ y)

  postulate

    -- _⊑_ "constructors".

    ⊑-refl             : (x : A ⊥) → x ⊑ x
    ⊑-trans            : {x y z : A ⊥} → x ⊑ y → y ⊑ z → x ⊑ z
    never⊑             : (x : A ⊥) → never ⊑ x
    upper-bound        : (s : Increasing-sequence A) →
                         Is-upper-bound s (⨆ s)
    least-upper-bound  : (s : Increasing-sequence A) (ub : A ⊥) →
                         Is-upper-bound s ub → ⨆ s ⊑ ub
    ⊑-proof-irrelevant : {x y : A ⊥} → Proof-irrelevant (x ⊑ y)

  -- Predicate transformer related to increasing sequences.

  Inc : ∀ {p q}
        (P : A ⊥ → Set p)
        (Q : ∀ {x y} → P x → P y → x ⊑ y → Set q) →
        Increasing-sequence A → Set (p ⊔ q)
  Inc P Q s =
    ∃ λ (p : ∀ n → P (s [ n ])) →
      ∀ n → Q (p n) (p (suc n)) (increasing s n)

-- Dependent eliminators.
--
-- I (NAD) have tried to follow the spirit of the rules for HITs
-- specified in the HoTT-Agda library
-- (https://github.com/HoTT/HoTT-Agda/blob/master/core/lib/types/HIT_README.txt).
-- However, at the time of writing those rules don't apply to indexed
-- types.

-- Record wrapping up the eliminators' arguments.

record Rec-args
         {p q} {A : Set a}
         (P : A ⊥ → Set p)
         (Q : ∀ {x y} → P x → P y → x ⊑ y → Set q) :
         Set (a ⊔ p ⊔ q) where
  field
    pe : P never
    po : ∀ x → P (now x)
    pl : ∀ s (pq : Inc P Q s) → P (⨆ s)
    pa : ∀ {x y} (x⊑y : x ⊑ y) (x⊒y : x ⊒ y)
         (p-x : P x) (p-y : P y)
         (q-x⊑y : Q p-x p-y x⊑y) (q-x⊒y : Q p-y p-x x⊒y) →
         subst P (antisymmetry x⊑y x⊒y) p-x ≡ p-y
    pp : ∀ {x} {p₁ p₂ : P x} → Proof-irrelevant (p₁ ≡ p₂)
    qr : ∀ x (p : P x) → Q p p (⊑-refl x)
    qt : ∀ {x y z} (x⊑y : x ⊑ y) (y⊑z : y ⊑ z) →
         (px : P x) (py : P y) (pz : P z) →
         Q px py x⊑y → Q py pz y⊑z → Q px pz (⊑-trans x⊑y y⊑z)
    qe : ∀ x (p : P x) → Q pe p (never⊑ x)
    qu : ∀ s (pq : Inc P Q s) n →
         Q (proj₁ pq n) (pl s pq) (upper-bound s n)
    ql : ∀ s ub is-ub (pq : Inc P Q s) (pu : P ub)
         (qu : ∀ n → Q (proj₁ pq n) pu (is-ub n)) →
         Q (pl s pq) pu (least-upper-bound s ub is-ub)
    qp : ∀ {x y} (p-x : P x) (p-y : P y) (x⊑y : x ⊑ y) →
         Proof-irrelevant (Q p-x p-y x⊑y)

-- The eliminators.

module _ {p q} {A : Set a}
         {P : A ⊥ → Set p}
         {Q : ∀ {x y} → P x → P y → x ⊑ y → Set q}
         (args : Rec-args P Q) where

  open Rec-args args

  postulate
    ⊥-rec : (x : A ⊥) → P x
    ⊑-rec : ∀ {x y} (x⊑y : x ⊑ y) → Q (⊥-rec x) (⊥-rec y) x⊑y

  inc-rec : (s : Increasing-sequence A) → Inc P Q s
  inc-rec (s , inc) = ( (λ n → ⊥-rec (s   n))
                      , (λ n → ⊑-rec (inc n))
                      )

  -- Computation rules for _⊥.
  --
  -- NOTE: Rewriting has not been activated for the "computation" rule
  -- corresponding to antisymmetry, and there is no computation rule
  -- corresponding to ≡-proof-irrelevant.

  postulate

    ⊥-rec-never : ⊥-rec never ≡ pe
    ⊥-rec-now   : ∀ x → ⊥-rec (now x) ≡ po x
    ⊥-rec-⨆     : ∀ s → ⊥-rec (⨆ s) ≡ pl s (inc-rec s)
    ⊥-rec-antisymmetry :
      ∀ {x y} (x⊑y : x ⊑ y) (x⊒y : x ⊒ y) →
      dependent-cong ⊥-rec (antisymmetry x⊑y x⊒y) ≡
      pa x⊑y x⊒y (⊥-rec x) (⊥-rec y) (⊑-rec x⊑y) (⊑-rec x⊒y)

  {-# REWRITE ⊥-rec-never #-}
  {-# REWRITE ⊥-rec-now   #-}
  {-# REWRITE ⊥-rec-⨆     #-}

  -- Computation rules for _⊑_.
  --
  -- NOTE: There is no computation rule corresponding to
  -- ⊑-proof-irrelevant.

  postulate

    ⊑-rec-⊑-refl            : ∀ x → ⊑-rec (⊑-refl x) ≡ qr x (⊥-rec x)
    ⊑-rec-⊑-trans           : ∀ {x y z} (x⊑y : x ⊑ y) (y⊑z : y ⊑ z) →
                              ⊑-rec (⊑-trans x⊑y y⊑z) ≡
                              qt x⊑y y⊑z
                                 (⊥-rec x) (⊥-rec y) (⊥-rec z)
                                 (⊑-rec x⊑y) (⊑-rec y⊑z)
    ⊑-rec-never⊑            : ∀ x → ⊑-rec (never⊑ x) ≡ qe x (⊥-rec x)
    ⊑-rec-upper-bound       : ∀ s n →
                              ⊑-rec (upper-bound s n) ≡
                              qu s (inc-rec s) n
    ⊑-rec-least-upper-bound : ∀ s ub is-ub →
                              ⊑-rec (least-upper-bound s ub is-ub) ≡
                              ql s ub is-ub
                                 (inc-rec s)
                                 (⊥-rec ub)
                                 (λ n → ⊑-rec (is-ub n))

  {-# REWRITE ⊑-rec-⊑-refl            #-}
  {-# REWRITE ⊑-rec-⊑-trans           #-}
  {-# REWRITE ⊑-rec-never⊑            #-}
  {-# REWRITE ⊑-rec-upper-bound       #-}
  {-# REWRITE ⊑-rec-least-upper-bound #-}
