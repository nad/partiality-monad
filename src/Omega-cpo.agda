------------------------------------------------------------------------
-- Pointed and non-pointed ω-cpos
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Omega-cpo where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Equality.Path.Isomorphisms equality-with-J
  using (ext; ⟨ext⟩)
open import Equivalence equality-with-J as Eq using (_≃_)
open import H-level equality-with-J hiding (Type)
open import H-level.Closure equality-with-J

open import Partiality-algebra as PA hiding (_∘_)
import Partiality-monad.Inductive.Monad.Adjunction as PA

-- Possibly non-pointed ω-cpos (with propositional ordering
-- relations).

record ω-cpo p q : Set (lsuc (p ⊔ q)) where

  infix 4 _⊑_

  -- Partial order axioms.

  field
    Carrier         : Set p
    _⊑_             : Carrier → Carrier → Set q
    reflexivity     : ∀ {x} → x ⊑ x
    antisymmetry    : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
    transitivity    : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
    ⊑-propositional : ∀ {x y} → Is-proposition (x ⊑ y)

  -- Increasing sequences.

  Increasing-sequence : Set (p ⊔ q)
  Increasing-sequence = ∃ λ (f : ℕ → Carrier) → ∀ n → f n ⊑ f (suc n)

  -- Projection functions for Increasing-sequence.

  infix 30 _[_]

  _[_] : Increasing-sequence → ℕ → Carrier
  _[_] = proj₁

  increasing : (s : Increasing-sequence) →
               ∀ n → (s [ n ]) ⊑ (s [ suc n ])
  increasing = proj₂

  -- Upper bounds.

  Is-upper-bound : Increasing-sequence → Carrier → Set q
  Is-upper-bound s x = ∀ n → (s [ n ]) ⊑ x

  -- Upper bound axioms.

  field
    ⨆                 : Increasing-sequence → Carrier
    upper-bound       : ∀ s → Is-upper-bound s (⨆ s)
    least-upper-bound : ∀ {s ub} → Is-upper-bound s ub → ⨆ s ⊑ ub

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

Set→ω-cpo : ∀ {ℓ} → SET ℓ → ω-cpo ℓ ℓ
Set→ω-cpo (A , A-set) = record
  { Carrier           = A
  ; _⊑_               = _≡_
  ; reflexivity       = refl
  ; antisymmetry      = const
  ; transitivity      = trans
  ; ⊑-propositional   = A-set
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

-- Pointed ω-cpos.

record ω-cppo p q : Set (lsuc (p ⊔ q)) where
  field
    cpo : ω-cpo p q

  open ω-cpo cpo public

  field
    least  : Carrier
    least⊑ : ∀ {x} → least ⊑ x

-- A pointed ω-CPO is equivalent to a partiality algebra over the
-- empty type.

ω-cppo≃ω-cppo : ∀ {p q} → ω-cppo p q ≃ PA.ω-cppo p q
ω-cppo≃ω-cppo = Eq.↔⇒≃ record
  { surjection = record
    { logical-equivalence = record
      { to   = λ X → let open ω-cppo X in record
                 { Type                    = Carrier
                 ; partiality-algebra-with = record
                   { _⊑_                = _⊑_
                   ; never              = least
                   ; now                = λ ()
                   ; ⨆                  = ⨆
                   ; antisymmetry       = antisymmetry
                   ; Type-is-set-unused = Carrier-is-set
                   ; ⊑-refl             = λ _ → reflexivity
                   ; ⊑-trans            = transitivity
                   ; never⊑             = λ _ → least⊑
                   ; upper-bound        = upper-bound
                   ; least-upper-bound  = λ _ _ → least-upper-bound
                   ; ⊑-propositional    = ⊑-propositional
                   }
                 }
      ; from = λ P → let open Partiality-algebra P in record
                 { cpo = record
                   { Carrier           = Type
                   ; _⊑_               = _⊑_
                   ; reflexivity       = ⊑-refl _
                   ; antisymmetry      = antisymmetry
                   ; transitivity      = ⊑-trans
                   ; ⊑-propositional   = ⊑-propositional
                   ; ⨆                 = ⨆
                   ; upper-bound       = upper-bound
                   ; least-upper-bound = least-upper-bound _ _
                   }
                 ; least  = never
                 ; least⊑ = never⊑ _
                 }
      }
    ; right-inverse-of = λ P →
        let open Partiality-algebra P in
        cong₂ (λ now (Type-is-set : Is-set Type) → record
                 { Type                    = Type
                 ; partiality-algebra-with = record
                   { _⊑_                = _⊑_
                   ; never              = never
                   ; now                = now
                   ; ⨆                  = ⨆
                   ; antisymmetry       = antisymmetry
                   ; Type-is-set-unused = Type-is-set
                   ; ⊑-refl             = ⊑-refl
                   ; ⊑-trans            = ⊑-trans
                   ; never⊑             = never⊑
                   ; upper-bound        = upper-bound
                   ; least-upper-bound  = least-upper-bound
                   ; ⊑-propositional    = ⊑-propositional
                   }
                 })
              (⟨ext⟩ λ ())
              (H-level-propositional ext 2 _ _)
    }
  ; left-inverse-of = λ _ → refl
  }
