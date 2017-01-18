------------------------------------------------------------------------
-- Pointed and non-pointed ω-cpos
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Omega-cpo where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Equivalence equality-with-J as Eq using (_≃_)
open import H-level equality-with-J hiding (Type)
open import H-level.Closure equality-with-J

-- Possibly non-pointed ω-cpos (with propositional ordering
-- relations).

record ω-cpo ℓ : Set (lsuc ℓ) where

  infix 4 _⊑_

  -- Partial order axioms.

  field
    Carrier            : Set ℓ
    _⊑_                : Carrier → Carrier → Set ℓ
    reflexivity        : ∀ {x} → x ⊑ x
    antisymmetry       : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
    transitivity       : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
    ⊑-proof-irrelevant : ∀ {x y} → Proof-irrelevant (x ⊑ y)

  -- Increasing sequences.

  Increasing-sequence : Set ℓ
  Increasing-sequence = ∃ λ (f : ℕ → Carrier) → ∀ n → f n ⊑ f (suc n)

  -- Projection functions for Increasing-sequence.

  infix 30 _[_]

  _[_] : Increasing-sequence → ℕ → Carrier
  _[_] = proj₁

  increasing : (s : Increasing-sequence) →
               ∀ n → (s [ n ]) ⊑ (s [ suc n ])
  increasing = proj₂

  -- Upper bounds.

  Is-upper-bound : Increasing-sequence → Carrier → Set ℓ
  Is-upper-bound s x = ∀ n → (s [ n ]) ⊑ x

  -- Upper bound axioms.

  field
    ⨆                 : Increasing-sequence → Carrier
    upper-bound       : ∀ s → Is-upper-bound s (⨆ s)
    least-upper-bound : ∀ {s ub} → Is-upper-bound s ub → ⨆ s ⊑ ub

  -- _⊑_ is propositional.

  ⊑-propositional : ∀ {x y} → Is-proposition (x ⊑ y)
  ⊑-propositional =
    _⇔_.from propositional⇔irrelevant ⊑-proof-irrelevant

  -- The carrier type is a set. (This lemma is analogous to
  -- Theorem 11.3.9 in "Homotopy Type Theory: Univalent Foundations of
  -- Mathematics" (first edition).)

  Carrier-is-set : Is-set Carrier
  Carrier-is-set = proj₁ $ Eq.propositional-identity≃≡
    (λ x y → x ⊑ y × y ⊑ x)
    (λ _ _ → ×-closure 1 ⊑-propositional ⊑-propositional)
    (λ _ → reflexivity , reflexivity)
    (λ x y → uncurry {B = λ _ → y ⊑ x} antisymmetry)

-- Every set can be turned into an ω-cpo.

Set→ω-cpo : ∀ {ℓ} → SET ℓ → ω-cpo ℓ
Set→ω-cpo (A , A-set) = record
  { Carrier            = A
  ; _⊑_                = _≡_
  ; reflexivity        = refl
  ; antisymmetry       = const
  ; transitivity       = trans
  ; ⊑-proof-irrelevant = _⇔_.to set⇔UIP A-set
  ; ⨆                  = (_$ 0) ∘ proj₁
  ; upper-bound        = uncurry upper-bound
  ; least-upper-bound  = _$ 0
  }
  where
  upper-bound : (f : ℕ → A) → (∀ n → f n ≡ f (suc n)) →
                ∀ n → f n ≡ f 0
  upper-bound f inc zero    = refl
  upper-bound f inc (suc n) =
    f (suc n)  ≡⟨ sym (inc n) ⟩
    f n        ≡⟨ upper-bound f inc n ⟩∎
    f 0        ∎

-- Pointed ω-cpos.

record ω-cppo ℓ : Set (lsuc ℓ) where
  field
    cpo : ω-cpo ℓ

  open ω-cpo cpo public

  field
    least  : Carrier
    least⊑ : ∀ {x} → least ⊑ x
