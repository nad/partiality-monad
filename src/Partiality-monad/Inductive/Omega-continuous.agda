------------------------------------------------------------------------
-- ω-continuous functions
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Partiality-monad.Inductive.Omega-continuous where

open import Equality.Propositional
open import Interval using (ext)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J
open import H-level.Closure equality-with-J

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Monotone

-- Definition of ω-continuous functions.

[_⊥→_⊥] : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
[ A ⊥→ B ⊥] = ∃ λ (f : [ A ⊥→ B ⊥]⊑) →
                ∀ s → proj₁ f (⨆ s) ≡ ⨆ [ f $ s ]-inc

-- Identity.

idω : ∀ {a} {A : Set a} → [ A ⊥→ A ⊥]
idω = id⊑ , λ _ → refl

-- Composition.

infixr 40 _∘ω_

_∘ω_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
       [ B ⊥→ C ⊥] → [ A ⊥→ B ⊥] → [ A ⊥→ C ⊥]
f ∘ω g = proj₁ f ∘⊑ proj₁ g , λ s →
  proj₁ (proj₁ f) (proj₁ (proj₁ g) (⨆ s))  ≡⟨ cong (proj₁ (proj₁ f)) (proj₂ g s) ⟩
  proj₁ (proj₁ f) (⨆ [ proj₁ g $ s ]-inc)  ≡⟨ proj₂ f _ ⟩∎
  ⨆ [ proj₁ f ∘⊑ proj₁ g $ s ]-inc         ∎

-- Equality characterisation lemma for ω-continuous functions.

equality-characterisation-continuous :
  ∀ {a b} {A : Set a} {B : Set b} {f g : [ A ⊥→ B ⊥]} →
  (∀ x → proj₁ (proj₁ f) x ≡ proj₁ (proj₁ g) x) ↔ f ≡ g
equality-characterisation-continuous {f = f} {g} =
  (∀ x → proj₁ (proj₁ f) x ≡ proj₁ (proj₁ g) x)  ↝⟨ equality-characterisation-monotone ⟩
  proj₁ f ≡ proj₁ g                              ↝⟨ ignore-propositional-component
                                                      (Π-closure ext 1 λ _ →
                                                       ⊥-is-set _ _) ⟩□
  f ≡ g                                          □

-- Composition is associative.

∘ω-assoc : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
           (f : [ C ⊥→ D ⊥]) (g : [ B ⊥→ C ⊥]) (h : [ A ⊥→ B ⊥]) →
           f ∘ω (g ∘ω h) ≡ (f ∘ω g) ∘ω h
∘ω-assoc _ _ _ =
  _↔_.to equality-characterisation-continuous λ _ → refl
