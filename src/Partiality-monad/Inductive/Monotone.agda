------------------------------------------------------------------------
-- Monotone functions
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Partiality-monad.Inductive.Monotone where

open import Equality.Propositional
open import Prelude

open import Bijection equality-with-J using (_↔_)

import Partiality-algebra.Monotone as M
open import Partiality-monad.Inductive

-- Definition of monotone functions.

[_⊥→_⊥]⊑ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
[ A ⊥→ B ⊥]⊑ = M.[ partiality-algebra A ⟶ partiality-algebra B ]⊑

module [_⊥→_⊥]⊑ {a b} {A : Set a} {B : Set b} (f : [ A ⊥→ B ⊥]⊑) =
  M.[_⟶_]⊑ f

open [_⊥→_⊥]⊑

-- Identity.

id⊑ : ∀ {a} {A : Set a} → [ A ⊥→ A ⊥]⊑
id⊑ = M.id⊑

-- Composition.

infixr 40 _∘⊑_

_∘⊑_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
       [ B ⊥→ C ⊥]⊑ → [ A ⊥→ B ⊥]⊑ → [ A ⊥→ C ⊥]⊑
_∘⊑_ = M._∘⊑_

-- Equality characterisation lemma for monotone functions.

equality-characterisation-monotone :
  ∀ {a b} {A : Set a} {B : Set b} {f g : [ A ⊥→ B ⊥]⊑} →
  (∀ x → function f x ≡ function g x) ↔ f ≡ g
equality-characterisation-monotone =
  M.equality-characterisation-monotone

-- Composition is associative.

∘⊑-assoc : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
           (f : [ C ⊥→ D ⊥]⊑) (g : [ B ⊥→ C ⊥]⊑) {h : [ A ⊥→ B ⊥]⊑} →
           f ∘⊑ (g ∘⊑ h) ≡ (f ∘⊑ g) ∘⊑ h
∘⊑-assoc = M.∘⊑-assoc

module _ {a b} {A : Set a} {B : Set b} where

  -- If a monotone function is applied to an increasing sequence,
  -- then the result is another increasing sequence.

  [_$_]-inc :
    [ A ⊥→ B ⊥]⊑ → Increasing-sequence A → Increasing-sequence B
  [_$_]-inc = M.[_$_]-inc

  -- A lemma relating monotone functions and least upper bounds.

  ⨆$⊑$⨆ : (f : [ A ⊥→ B ⊥]⊑) →
          ∀ s → ⨆ [ f $ s ]-inc ⊑ function f (⨆ s)
  ⨆$⊑$⨆ = M.⨆$⊑$⨆
