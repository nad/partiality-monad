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
open import Univalence-axiom equality-with-J

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

  evalP : (∃ λ n → Tm n × Env n) → M Value
  evalP (_ , t , ρ) = ⟦ t ⟧′ ρ

  eval : Trans-⊑ (∃ λ n → Tm n × Env n) Value
  eval = transformer evalP

  ⟦_⟧ : ∀ {n} → Tm n → Env n → Value ⊥
  ⟦ t ⟧ ρ = fixP evalP (_ , t , ρ)

------------------------------------------------------------------------
-- The two interpreters are pointwise equal

-- Both interpreters' bodies have the form ⨆ s for some sequences s,
-- and element n in the first interpreter's sequence is equal to
-- element 1 + n in the second interpreter's sequence (when the
-- arguments are equal).

interpreters-equal :
  ∀ {n} (t : Tm n) ρ →
  Interpreter₁.⟦ t ⟧ ρ ≡ Interpreter₂.⟦ t ⟧ ρ
interpreters-equal = λ t ρ →
                                                                 $⟨ ⟦⟧-lemma t ρ ⟩
  (∀ n → Interpreter₁.⟦ t ⟧′ ρ n ≡
         app→ (function Interpreter₂.eval) (suc n) (_ , t , ρ))  ↝⟨ cong ⨆ ∘ _↔_.to equality-characterisation-increasing ⟩

  ⨆ (Interpreter₁.⟦ t ⟧ˢ ρ) ≡
  ⨆ (tailˢ (fix→-sequence Interpreter₂.eval (_ , t , ρ)))        ↝⟨ flip trans (⨆tail≡⨆ _) ⟩

  ⨆ (Interpreter₁.⟦ t ⟧ˢ ρ) ≡
  ⨆ (fix→-sequence Interpreter₂.eval (_ , t , ρ))                ↝⟨ id ⟩□

  Interpreter₁.⟦ t ⟧ ρ ≡ Interpreter₂.⟦ t ⟧ ρ                    □
  where
  open Partial
  open Trans-⊑

  mutual

    ⟦⟧-lemma :
      ∀ {n} (t : Tm n) ρ n →
      Interpreter₁.⟦ t ⟧′ ρ n ≡
      function (Interpreter₂.⟦ t ⟧′ ρ)
               (app→ (function Interpreter₂.eval) n)
    ⟦⟧-lemma (var x)   ρ n = refl
    ⟦⟧-lemma (ƛ t)     ρ n = refl
    ⟦⟧-lemma (t₁ · t₂) ρ n =
      cong₂ _>>=_ (⟦⟧-lemma t₁ ρ n) $ ext λ v₁ →
      cong₂ _>>=_ (⟦⟧-lemma t₂ ρ n) $ ext λ v₂ →
      ∙-lemma v₁ v₂ n

    ∙-lemma :
      ∀ v₁ v₂ n →
      (v₁ Interpreter₁.∙ v₂) n ≡
      function (v₁ Interpreter₂.∙ v₂)
               (app→ (function Interpreter₂.eval) n)
    ∙-lemma (ƛ t₁ ρ) v₂ zero    = refl
    ∙-lemma (ƛ t₁ ρ) v₂ (suc n) = ⟦⟧-lemma t₁ (snoc ρ v₂) n

------------------------------------------------------------------------
-- An example

-- The semantics of Ω is the non-terminating computation never.

-- A proof for Interpreter₁.

Ω-loops₁ : Interpreter₁.⟦ Ω ⟧ empty ≡ never
Ω-loops₁ =
  antisymmetry (least-upper-bound _ _ lemma) (never⊑ _)
  where
  open Interpreter₁

  lemma : ∀ n → ⟦ Ω ⟧′ empty n ⊑ never
  lemma zero    = never⊑ never
  lemma (suc n) = lemma n

-- A direct proof for Interpreter₂.

Ω-loops₂ : Interpreter₂.⟦ Ω ⟧ empty ≡ never
Ω-loops₂ = antisymmetry (least-upper-bound _ _ lemma) (never⊑ _)
  where
  open Interpreter₂
  open Trans-⊑

  lemma : ∀ n → app→ (function eval) n (_ , Ω , empty) ⊑ never
  lemma zero          = never⊑ never
  lemma (suc zero)    = never⊑ never
  lemma (suc (suc n)) =
    app→ (function eval) (suc (suc n)) (_ , Ω , empty)  ⊑⟨⟩
    app→ (function eval) (suc n) (_ , Ω , empty)        ⊑⟨ lemma (suc n) ⟩■
    never                                               ■

-- Another proof for Interpreter₂. This proof uses Scott induction
-- (and univalence).

Ω-loops₂′ : Univalence lzero → Interpreter₂.⟦ Ω ⟧ empty ≡ never
Ω-loops₂′ univ = antisymmetry lemma (never⊑ _)
  where
  open Interpreter₂
  open Trans-⊑

  lemma =
    ⟦ Ω ⟧ empty                                 ⊑⟨⟩
    fixP evalP (_ , Ω , empty)                  ⊑⟨ cong (_$ (_ , Ω , empty)) $
                                                     fixP-is-fixpoint-combinator univ evalP ⟩≡
    function eval (fixP evalP) (_ , Ω , empty)  ⊑⟨ fixP-induction₁
                                                     (λ f → function eval f (_ , Ω , empty) ⊑ never)
                                                     (never⊑ never)
                                                     (λ s hyp →
                                                        function eval (⨆ ∘ s) (_ , Ω , empty)  ⊑⟨ least-upper-bound _ _ hyp ⟩■
                                                        never                                  ■)
                                                     evalP
                                                     (λ g hyp →
                                                        function eval (function eval g) (_ , Ω , empty)  ⊑⟨⟩
                                                        function eval g (_ , Ω , empty)                  ⊑⟨ hyp ⟩■
                                                        never                                            ■) ⟩■
    never                                       ■

------------------------------------------------------------------------
-- Setup

-- Let us use Interpreter₂ as the default interpreter.

open Interpreter₂ public