------------------------------------------------------------------------
-- Monotone functions
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Partiality-monad.Inductive.Monotone where

open import Equality.Propositional
open import Interval using (ext)
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
import Equivalence equality-with-J as Eq
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level.Closure equality-with-J

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Properties

-- Definition of monotone functions.

[_⊥→_⊥]⊑ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
[ A ⊥→ B ⊥]⊑ = ∃ λ (f : A ⊥ → B ⊥) → ∀ {x y} → x ⊑ y → f x ⊑ f y

-- Identity.

id⊑ : ∀ {a} {A : Set a} → [ A ⊥→ A ⊥]⊑
id⊑ = id , id

-- Composition.

infixr 40 _∘⊑_

_∘⊑_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
       [ B ⊥→ C ⊥]⊑ → [ A ⊥→ B ⊥]⊑ → [ A ⊥→ C ⊥]⊑
f ∘⊑ g = proj₁ f ∘ proj₁ g
       , proj₂ f ∘ proj₂ g

-- Equality characterisation lemma for monotone functions.

equality-characterisation-monotone :
  ∀ {a b} {A : Set a} {B : Set b} {f g : [ A ⊥→ B ⊥]⊑} →
  (∀ x → proj₁ f x ≡ proj₁ g x) ↔ f ≡ g
equality-characterisation-monotone {f = f} {g} =
  (∀ x → proj₁ f x ≡ proj₁ g x)  ↔⟨ Eq.extensionality-isomorphism ext ⟩
  proj₁ f ≡ proj₁ g              ↝⟨ ignore-propositional-component
                                      (implicit-Π-closure ext 1 λ _ →
                                       implicit-Π-closure ext 1 λ _ →
                                       Π-closure          ext 1 λ _ →
                                       ⊑-propositional) ⟩□
  f ≡ g                          □

-- Composition is associative.

∘⊑-assoc : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
           (f : [ C ⊥→ D ⊥]⊑) (g : [ B ⊥→ C ⊥]⊑) {h : [ A ⊥→ B ⊥]⊑} →
           f ∘⊑ (g ∘⊑ h) ≡ (f ∘⊑ g) ∘⊑ h
∘⊑-assoc _ _ =
  _↔_.to equality-characterisation-monotone λ _ → refl

module _ {a b} {A : Set a} {B : Set b} where

  -- If a monotone function is applied to an increasing sequence,
  -- then the result is another increasing sequence.

  [_$_]-inc :
    [ A ⊥→ B ⊥]⊑ → Increasing-sequence A → Increasing-sequence B
  [ f $ s ]-inc = (λ n → proj₁ f (s [ n ]))
                , (λ n → proj₂ f (increasing s n))

  -- A lemma relating monotone functions and least upper bounds.

  ⨆$⊑$⨆ : (f : [ A ⊥→ B ⊥]⊑) →
          ∀ s → ⨆ [ f $ s ]-inc ⊑ proj₁ f (⨆ s)
  ⨆$⊑$⨆ f s = least-upper-bound _ _ (λ n →

    [ f $ s ]-inc [ n ]  ⊑⟨ proj₂ f (

      s [ n ]                 ⊑⟨ upper-bound _ _ ⟩■
      ⨆ s                     ■) ⟩■

    proj₁ f (⨆ s)        ■)
