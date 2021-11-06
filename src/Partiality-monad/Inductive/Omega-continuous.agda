------------------------------------------------------------------------
-- ω-continuous functions
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

module Partiality-monad.Inductive.Omega-continuous where

open import Equality.Propositional
open import Prelude

open import Bijection equality-with-J using (_↔_)

import Partiality-algebra.Omega-continuous as O
open import Partiality-monad.Inductive

-- Definition of ω-continuous functions.

[_⊥→_⊥] : ∀ {a b} → Type a → Type b → Type (a ⊔ b)
[ A ⊥→ B ⊥] = O.[ partiality-algebra A ⟶ partiality-algebra B ]

module [_⊥→_⊥] {a b} {A : Type a} {B : Type b} (f : [ A ⊥→ B ⊥]) =
  O.[_⟶_] f

open [_⊥→_⊥]

-- Identity.

idω : ∀ {a} {A : Type a} → [ A ⊥→ A ⊥]
idω = O.idω

-- Composition.

infixr 40 _∘ω_

_∘ω_ : ∀ {a b c} {A : Type a} {B : Type b} {C : Type c} →
       [ B ⊥→ C ⊥] → [ A ⊥→ B ⊥] → [ A ⊥→ C ⊥]
_∘ω_ = O._∘ω_

-- Equality characterisation lemma for ω-continuous functions.

equality-characterisation-continuous :
  ∀ {a b} {A : Type a} {B : Type b} {f g : [ A ⊥→ B ⊥]} →
  (∀ x → function f x ≡ function g x) ↔ f ≡ g
equality-characterisation-continuous =
  O.equality-characterisation-continuous

-- Composition is associative.

∘ω-assoc :
  ∀ {a b c d} {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  (f : [ C ⊥→ D ⊥]) (g : [ B ⊥→ C ⊥]) (h : [ A ⊥→ B ⊥]) →
  f ∘ω (g ∘ω h) ≡ (f ∘ω g) ∘ω h
∘ω-assoc = O.∘ω-assoc
