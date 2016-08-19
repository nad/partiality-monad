------------------------------------------------------------------------
-- Pointed and non-pointed ω-CPOs
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Omega-CPO where

open import Equality.Propositional
open import Prelude

-- Possibly non-pointed ω-CPOs.

record ω-CPO ℓ : Set (lsuc ℓ) where

  infix 4 _⊑_

  -- Partial order axioms.

  field
    Carrier      : Set ℓ
    _⊑_          : Carrier → Carrier → Set ℓ
    reflexivity  : ∀ {x} → x ⊑ x
    antisymmetry : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
    transitivity : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z

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

-- Every type can be turned into an ω-CPO.

Type→ω-CPO : ∀ {ℓ} → Set ℓ → ω-CPO ℓ
Type→ω-CPO A = record
  { Carrier           = A
  ; _⊑_               = _≡_
  ; reflexivity       = refl
  ; antisymmetry      = const
  ; transitivity      = trans
  ; ⨆                 = (_$ 0) ∘ proj₁
  ; upper-bound       = uncurry upper-bound
  ; least-upper-bound = _$ 0
  }
  where
  upper-bound : (f : ℕ → A) → (∀ n → f n ≡ f (suc n)) →
                ∀ n → f n ≡ f 0
  upper-bound f inc zero    = refl
  upper-bound f inc (suc n) =
    f (suc n)  ≡⟨ sym (inc n) ⟩
    f n        ≡⟨ upper-bound f inc n ⟩∎
    f 0        ∎

-- Pointed ω-CPOs.

record ω-CPPO ℓ : Set (lsuc ℓ) where
  field
    cpo : ω-CPO ℓ

  open ω-CPO cpo public

  field
    least  : Carrier
    least⊑ : ∀ {x} → least ⊑ x
