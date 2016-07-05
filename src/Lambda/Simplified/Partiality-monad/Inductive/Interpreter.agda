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

  infix 10 _∙_ _∙ˢ_

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

  _∙ˢ_ : Value → Value → Increasing-sequence Value
  v₁ ∙ˢ v₂ = v₁ ∙ v₂ , ∙-increasing v₁ v₂

  ⟦_⟧ : ∀ {n} → Tm n → Env n → Value ⊥
  ⟦ t ⟧ ρ = ⨆ (⟦ t ⟧ˢ ρ)

------------------------------------------------------------------------
-- Another interpreter

module Interpreter₂ where

  -- This interpreter is defined using a fixpoint combinator.

  module _ (rec : (∃ λ n → Tm n × Env n) → Value ⊥) where

    infix 10 _∙_

    _∙_ : Value → Value → Value ⊥
    ƛ t₁ ρ ∙ v₂ = rec (_ , t₁ , snoc ρ v₂)

    ⟦_⟧′ : ∀ {n} → Tm n → Env n → Value ⊥
    ⟦ var x ⟧′   ρ = return (ρ x)
    ⟦ ƛ t ⟧′     ρ = return (ƛ t ρ)
    ⟦ t₁ · t₂ ⟧′ ρ = ⟦ t₁ ⟧′ ρ >>= λ v₁ →
                     ⟦ t₂ ⟧′ ρ >>= λ v₂ →
                     v₁ ∙ v₂

  ∙-mono : ∀ {rec₁ rec₂} →
           (∀ x → rec₁ x ⊑ rec₂ x) →
           ∀ v₁ v₂ → _∙_ rec₁ v₁ v₂ ⊑ _∙_ rec₂ v₁ v₂
  ∙-mono rec₁⊑rec₂ (ƛ t₁ ρ) v₂ = rec₁⊑rec₂ (_ , t₁ , snoc ρ v₂)

  ⟦⟧′-mono : ∀ {rec₁ rec₂} →
             (∀ x → rec₁ x ⊑ rec₂ x) →
             ∀ {n} (t : Tm n) ρ → ⟦_⟧′ rec₁ t ρ ⊑ ⟦_⟧′ rec₂ t ρ
  ⟦⟧′-mono rec₁⊑rec₂ (var x)   ρ = return (ρ x)   ■
  ⟦⟧′-mono rec₁⊑rec₂ (ƛ t)     ρ = return (ƛ t ρ) ■
  ⟦⟧′-mono rec₁⊑rec₂ (t₁ · t₂) ρ =
    ⟦⟧′-mono rec₁⊑rec₂ t₁ ρ >>=-mono λ v₁ →
    ⟦⟧′-mono rec₁⊑rec₂ t₂ ρ >>=-mono λ v₂ →
    ∙-mono rec₁⊑rec₂ v₁ v₂

  step : ((∃ λ n → Tm n × Env n) → Value ⊥) →
         ((∃ λ n → Tm n × Env n) → Value ⊥)
  step rec (_ , t , ρ) = ⟦_⟧′ rec t ρ

  step-mono :
    {rec₁ rec₂ : (∃ λ n → Tm n × Env n) → Value ⊥} →
    (∀ x → rec₁ x ⊑ rec₂ x) →
    ∀ x → step rec₁ x ⊑ step rec₂ x
  step-mono rec₁⊑rec₂ (_ , t , ρ) = ⟦⟧′-mono rec₁⊑rec₂ t ρ

  ⟦_⟧ : ∀ {n} → Tm n → Env n → Value ⊥
  ⟦ t ⟧ ρ = fix→ (step , step-mono) (_ , t , ρ)

------------------------------------------------------------------------
-- The two interpreters are pointwise equal

interpreters-equal :
  ∀ {n} (t : Tm n) ρ →
  Interpreter₁.⟦ t ⟧ ρ ≡ Interpreter₂.⟦ t ⟧ ρ
interpreters-equal = λ t ρ →
                                                                        $⟨ ⟦⟧-lemma t ρ ⟩
  (∀ n → Interpreter₁.⟦ t ⟧′ ρ n ≡
         app Interpreter₂.step (suc n) (_ , t , ρ))                     ↝⟨ cong ⨆ ∘ _↔_.to equality-characterisation-increasing ⟩

  ⨆ (Interpreter₁.⟦ t ⟧ˢ ρ) ≡
  ⨆ (tailˢ (fix→-sequence (Interpreter₂.step , Interpreter₂.step-mono)
                          (_ , t , ρ)))                                 ↝⟨ flip trans (⨆tail≡⨆ _) ⟩

  ⨆ (Interpreter₁.⟦ t ⟧ˢ ρ) ≡
  ⨆ (fix→-sequence (Interpreter₂.step , Interpreter₂.step-mono)
                   (_ , t , ρ))                                         ↝⟨ id ⟩□

  Interpreter₁.⟦ t ⟧ ρ ≡ Interpreter₂.⟦ t ⟧ ρ                           □
  where
  mutual

    ⟦⟧-lemma :
      ∀ {n} (t : Tm n) ρ n →
      Interpreter₁.⟦ t ⟧′ ρ n ≡
      app Interpreter₂.step (suc n) (_ , t , ρ)
    ⟦⟧-lemma (var x)   ρ n = refl
    ⟦⟧-lemma (ƛ t)     ρ n = refl
    ⟦⟧-lemma (t₁ · t₂) ρ n =
      cong₂ _>>=_ (⟦⟧-lemma t₁ ρ n) $ ext λ v₁ →
      cong₂ _>>=_ (⟦⟧-lemma t₂ ρ n) $ ext λ v₂ →
      ∙-lemma v₁ v₂ n

    ∙-lemma :
      ∀ v₁ v₂ n →
      Interpreter₁._∙_ v₁ v₂ n ≡
      Interpreter₂._∙_ (app Interpreter₂.step n) v₁ v₂
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
