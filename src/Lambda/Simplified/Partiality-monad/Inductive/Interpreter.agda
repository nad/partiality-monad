------------------------------------------------------------------------
-- A definitional interpreter
------------------------------------------------------------------------

{-# OPTIONS --without-K --rewriting #-}

module Lambda.Simplified.Partiality-monad.Inductive.Interpreter where

open import Equality.Propositional
open import Interval using (ext)
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J hiding (id; _∘_)
open import Monad equality-with-J

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Fixpoints
open import Partiality-monad.Inductive.Monad
open import Partiality-monad.Inductive.Properties

open import Lambda.Simplified.Syntax

open Closure Tm

------------------------------------------------------------------------
-- One interpreter

module Interpreter₁ where

  -- This interpreter is defined as the least upper bound of a
  -- sequence of increasingly defined interpreters.

  infix 10 _∙_

  mutual

    ⟦_⟧′ : ∀ {n} → Tm n → Env n → ℕ → Value ⊥
    ⟦ var x ⟧′   ρ n = return (ρ x)
    ⟦ ƛ t ⟧′     ρ n = return (ƛ t ρ)
    ⟦ t₁ · t₂ ⟧′ ρ n = ⟦ t₁ ⟧′ ρ n >>= λ v₁ →
                       ⟦ t₂ ⟧′ ρ n >>= λ v₂ →
                       (v₁ ∙ v₂) n

    _∙_ : Value → Value → ℕ → Value ⊥
    (ƛ t₁ ρ ∙ v₂) zero    = never
    (ƛ t₁ ρ ∙ v₂) (suc n) = ⟦ t₁ ⟧′ (snoc ρ v₂) n

  mutual

    ⟦⟧′-increasing :
      ∀ {n} (t : Tm n) ρ n → ⟦ t ⟧′ ρ n ⊑ ⟦ t ⟧′ ρ (suc n)
    ⟦⟧′-increasing (var x)   ρ n = return (ρ x)   ■
    ⟦⟧′-increasing (ƛ t)     ρ n = return (ƛ t ρ) ■
    ⟦⟧′-increasing (t₁ · t₂) ρ n =
      ⟦⟧′-increasing t₁ ρ n >>=-mono λ v₁ →
      ⟦⟧′-increasing t₂ ρ n >>=-mono λ v₂ →
      ∙-increasing v₁ v₂ n

    ∙-increasing : ∀ v₁ v₂ n → (v₁ ∙ v₂) n ⊑ (v₁ ∙ v₂) (suc n)
    ∙-increasing (ƛ t₁ ρ) v₂ (suc n) = ⟦⟧′-increasing t₁ (snoc ρ v₂) n
    ∙-increasing (ƛ t₁ ρ) v₂ zero    =
      never                  ⊑⟨ never⊑ _ ⟩■
      ⟦ t₁ ⟧′ (snoc ρ v₂) 0  ■

  ⟦_⟧ˢ : ∀ {n} → Tm n → Env n → Increasing-sequence Value
  ⟦ t ⟧ˢ ρ = ⟦ t ⟧′ ρ , ⟦⟧′-increasing t ρ

  ⟦_⟧ : ∀ {n} → Tm n → Env n → Value ⊥
  ⟦ t ⟧ ρ = ⨆ (⟦ t ⟧ˢ ρ)

------------------------------------------------------------------------
-- Another interpreter

module Interpreter₂ where

  -- This interpreter is defined using a fixpoint combinator.

  M : Set → Set₁
  M = Partial (∃ λ n → Tm n × Env n) Value

  infix 10 _∙_

  _∙_ : Value → Value → M Value
  ƛ t₁ ρ ∙ v₂ = rec (_ , t₁ , snoc ρ v₂)

  ⟦_⟧′ : ∀ {n} → Tm n → Env n → M Value
  ⟦ var x ⟧′   ρ = return (ρ x)
  ⟦ ƛ t ⟧′     ρ = return (ƛ t ρ)
  ⟦ t₁ · t₂ ⟧′ ρ = ⟦ t₁ ⟧′ ρ >>= λ v₁ →
                   ⟦ t₂ ⟧′ ρ >>= λ v₂ →
                   v₁ ∙ v₂

  ⟦_⟧ : ∀ {n} → Tm n → Env n → Value ⊥
  ⟦ t ⟧ ρ = fixP (λ { (_ , t , ρ) → ⟦ t ⟧′ ρ }) (_ , t , ρ)

------------------------------------------------------------------------
-- The two interpreters are pointwise equal

interpreters-equal :
  ∀ {n} (t : Tm n) ρ →
  Interpreter₁.⟦ t ⟧ ρ ≡ Interpreter₂.⟦ t ⟧ ρ
interpreters-equal = λ t ρ →
                                                     $⟨ ⟦⟧-lemma t ρ ⟩
  (∀ n → Interpreter₁.⟦ t ⟧′ ρ n ≡
         app→ (function step₂) (suc n) (_ , t , ρ))  ↝⟨ cong ⨆ ∘ _↔_.to equality-characterisation-increasing ⟩

  ⨆ (Interpreter₁.⟦ t ⟧ˢ ρ) ≡
  ⨆ (tailˢ (fix→-sequence step₂ (_ , t , ρ)))        ↝⟨ flip trans (⨆tail≡⨆ _) ⟩

  ⨆ (Interpreter₁.⟦ t ⟧ˢ ρ) ≡
  ⨆ (fix→-sequence step₂ (_ , t , ρ))                ↝⟨ id ⟩□

  Interpreter₁.⟦ t ⟧ ρ ≡ Interpreter₂.⟦ t ⟧ ρ        □
  where
  open Partial
  open Trans-⊑

  step₂ : Trans-⊑ (∃ λ n → Tm n × Env n) Value
  step₂ = transformer λ { (_ , t , ρ) → Interpreter₂.⟦ t ⟧′ ρ }

  mutual

    ⟦⟧-lemma :
      ∀ {n} (t : Tm n) ρ n →
      Interpreter₁.⟦ t ⟧′ ρ n ≡
      function (Interpreter₂.⟦ t ⟧′ ρ) (app→ (function step₂) n)
    ⟦⟧-lemma (var x)   ρ n = refl
    ⟦⟧-lemma (ƛ t)     ρ n = refl
    ⟦⟧-lemma (t₁ · t₂) ρ n =
      cong₂ _>>=_ (⟦⟧-lemma t₁ ρ n) $ ext λ v₁ →
      cong₂ _>>=_ (⟦⟧-lemma t₂ ρ n) $ ext λ v₂ →
      ∙-lemma v₁ v₂ n

    ∙-lemma :
      ∀ v₁ v₂ n →
      (v₁ Interpreter₁.∙ v₂) n ≡
      function (v₁ Interpreter₂.∙ v₂) (app→ (function step₂) n)
    ∙-lemma (ƛ t₁ ρ) v₂ zero    = refl
    ∙-lemma (ƛ t₁ ρ) v₂ (suc n) = ⟦⟧-lemma t₁ (snoc ρ v₂) n

-- Let us use Interpreter₁ as the default interpreter.

open Interpreter₁ public

------------------------------------------------------------------------
-- An example

-- The semantics of Ω is the non-terminating computation never.

Ω-loops : ⟦ Ω ⟧ empty ≡ never
Ω-loops =
  antisymmetry (least-upper-bound _ _ lemma) (never⊑ _)
  where
  lemma : ∀ n → ⟦ Ω ⟧′ empty n ⊑ never
  lemma zero    = never⊑ never
  lemma (suc n) = lemma n
