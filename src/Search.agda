------------------------------------------------------------------------
-- An example: A function that, given a stream, tries to find an
-- element satisfying a predicate
------------------------------------------------------------------------

{-# OPTIONS --cubical #-}

module Search where

open import Equality.Propositional
open import Prelude hiding (⊥)

open import Equality.Path.Isomorphisms equality-with-J using (⟨ext⟩)
open import Monad equality-with-J
open import Univalence-axiom equality-with-J

open import Partiality-algebra.Monotone
open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Fixpoints
open import Partiality-monad.Inductive.Monad

-- Streams.

infixr 5 _∷_

record Stream {a} (A : Set a) : Set a where
  coinductive
  constructor _∷_
  field
    head : A
    tail : Stream A

open Stream

-- A direct implementation of the function.

module Direct {a} {A : Set a} (q : A → Bool) where

  Φ : Trans (Stream A) (λ _ → A)
  Φ f xs = if q (head xs) then return (head xs) else f (tail xs)

  Φ-monotone :
    ∀ {f₁ f₂} → (∀ xs → f₁ xs ⊑ f₂ xs) → ∀ xs → Φ f₁ xs ⊑ Φ f₂ xs
  Φ-monotone f₁⊑f₂ xs with q (head xs)
  ... | true  = return (head xs)  ■
  ... | false = f₁⊑f₂ (tail xs)

  Φ-⊑ : Trans-⊑ (Stream A) (λ _ → A)
  Φ-⊑ = record { function = Φ; monotone = Φ-monotone }

  search : Stream A → A ⊥
  search = fix→ Φ-⊑

  search-least :
    ∀ f → (∀ xs → Φ f xs ⊑ f xs) →
    ∀ xs → search xs ⊑ f xs
  search-least = fix→-is-least Φ-⊑

  Φ-ω-continuous :
    (s : ∃ λ (f : ℕ → Stream A → A ⊥) →
           ∀ n xs → f n xs ⊑ f (suc n) xs) →
    Φ (⨆ ∘ at s) ≡ ⨆ ∘ at [ Φ-⊑ $ s ]-inc
  Φ-ω-continuous s = ⟨ext⟩ helper
    where
    helper : ∀ xs → Φ (⨆ ∘ at s) xs ≡ ⨆ (at [ Φ-⊑ $ s ]-inc xs)
    helper xs with q (head xs)
    ... | true  = return (head xs)               ≡⟨ sym ⨆-const ⟩∎
                  ⨆ (constˢ (return (head xs)))  ∎
    ... | false = ⨆ (at s (tail xs))             ∎

  Φ-ω : Trans-ω (Stream A) (λ _ → A)
  Φ-ω = record
    { monotone-function = Φ-⊑
    ; ω-continuous      = Φ-ω-continuous
    }

  search-fixpoint : search ≡ Φ search
  search-fixpoint = fix→-is-fixpoint-combinator Φ-ω

-- An arguably more convenient implementation.

module Indirect {a} {A : Set a} (q : A → Bool) where

  ΦP : Stream A → Partial (Stream A) (λ _ → A) A
  ΦP xs =
    if q (head xs) then
      return (head xs)
    else
      rec (tail xs)

  Φ : Trans (Stream A) (λ _ → A)
  Φ = Trans-⊑.function (transformer ΦP)

  search : Stream A → A ⊥
  search = fixP ΦP

  search-least :
    ∀ f → (∀ xs → Φ f xs ⊑ f xs) →
    ∀ xs → search xs ⊑ f xs
  search-least = fixP-is-least ΦP

  search-fixpoint : search ≡ Φ search
  search-fixpoint = fixP-is-fixpoint-combinator ΦP
