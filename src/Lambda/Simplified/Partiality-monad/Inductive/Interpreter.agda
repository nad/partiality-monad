------------------------------------------------------------------------
-- A definitional interpreter
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Lambda.Simplified.Partiality-monad.Inductive.Interpreter where

open import Equality.Propositional
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms equality-with-J using (⟨ext⟩)
open import Function-universe equality-with-J hiding (id; _∘_)
open import Monad equality-with-J
open import Univalence-axiom equality-with-J
open import Vec.Function equality-with-J

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Fixpoints
open import Partiality-monad.Inductive.Monad

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
    (ƛ t₁ ρ ∙ v₂) (suc n) = ⟦ t₁ ⟧′ (cons v₂ ρ) n

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
    ∙-increasing (ƛ t₁ ρ) v₂ (suc n) = ⟦⟧′-increasing t₁ (cons v₂ ρ) n
    ∙-increasing (ƛ t₁ ρ) v₂ zero    =
      never                  ⊑⟨ never⊑ _ ⟩■
      ⟦ t₁ ⟧′ (cons v₂ ρ) 0  ■

  ⟦_⟧ˢ : ∀ {n} → Tm n → Env n → Increasing-sequence Value
  ⟦ t ⟧ˢ ρ = ⟦ t ⟧′ ρ , ⟦⟧′-increasing t ρ

  ⟦_⟧ : ∀ {n} → Tm n → Env n → Value ⊥
  ⟦ t ⟧ ρ = ⨆ (⟦ t ⟧ˢ ρ)

------------------------------------------------------------------------
-- Another interpreter

module Interpreter₂ where

  -- This interpreter is defined using a fixpoint combinator.

  M : Set → Set₁
  M = Partial (∃ λ n → Tm n × Env n) (λ _ → Value)

  infix 10 _∙_

  _∙_ : Value → Value → M Value
  ƛ t₁ ρ ∙ v₂ = rec (_ , t₁ , cons v₂ ρ)

  ⟦_⟧′ : ∀ {n} → Tm n → Env n → M Value
  ⟦ var x ⟧′   ρ = return (ρ x)
  ⟦ ƛ t ⟧′     ρ = return (ƛ t ρ)
  ⟦ t₁ · t₂ ⟧′ ρ = ⟦ t₁ ⟧′ ρ >>= λ v₁ →
                   ⟦ t₂ ⟧′ ρ >>= λ v₂ →
                   v₁ ∙ v₂

  evalP : (∃ λ n → Tm n × Env n) → M Value
  evalP (_ , t , ρ) = ⟦ t ⟧′ ρ

  eval : Trans-⊑ (∃ λ n → Tm n × Env n) (λ _ → Value)
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
         app→ Interpreter₂.eval (suc n) (_ , t , ρ))            ↝⟨ cong ⨆ ∘ _↔_.to equality-characterisation-increasing ⟩

  ⨆ (Interpreter₁.⟦ t ⟧ˢ ρ) ≡
  ⨆ (tailˢ (at (fix→-sequence Interpreter₂.eval) (_ , t , ρ)))  ↝⟨ flip trans (⨆tail≡⨆ _) ⟩

  ⨆ (Interpreter₁.⟦ t ⟧ˢ ρ) ≡
  ⨆ (at (fix→-sequence Interpreter₂.eval) (_ , t , ρ))          ↝⟨ id ⟩□

  Interpreter₁.⟦ t ⟧ ρ ≡ Interpreter₂.⟦ t ⟧ ρ                   □
  where
  open Partial
  open Trans-⊑

  mutual

    ⟦⟧-lemma :
      ∀ {n} (t : Tm n) ρ n →
      Interpreter₁.⟦ t ⟧′ ρ n ≡
      function (Interpreter₂.⟦ t ⟧′ ρ)
               (app→ Interpreter₂.eval n)
    ⟦⟧-lemma (var x)   ρ n = refl
    ⟦⟧-lemma (ƛ t)     ρ n = refl
    ⟦⟧-lemma (t₁ · t₂) ρ n =
      cong₂ _>>=_ (⟦⟧-lemma t₁ ρ n) $ ⟨ext⟩ λ v₁ →
      cong₂ _>>=_ (⟦⟧-lemma t₂ ρ n) $ ⟨ext⟩ λ v₂ →
      ∙-lemma v₁ v₂ n

    ∙-lemma :
      ∀ v₁ v₂ n →
      (v₁ Interpreter₁.∙ v₂) n ≡
      function (v₁ Interpreter₂.∙ v₂)
               (app→ Interpreter₂.eval n)
    ∙-lemma (ƛ t₁ ρ) v₂ zero    = refl
    ∙-lemma (ƛ t₁ ρ) v₂ (suc n) = ⟦⟧-lemma t₁ (cons v₂ ρ) n

------------------------------------------------------------------------
-- An example

-- The semantics of Ω is the non-terminating computation never.

-- A proof for Interpreter₁.

Ω-loops₁ : Interpreter₁.⟦ Ω ⟧ nil ≡ never
Ω-loops₁ =
  antisymmetry (least-upper-bound _ _ lemma) (never⊑ _)
  where
  open Interpreter₁

  ω-nil = ƛ (var fzero · var fzero) nil

  reduce-twice :
    ∀ n → ⟦ Ω ⟧′ nil n ≡ (ω-nil ∙ ω-nil) n
  reduce-twice n =
    ⟦ Ω ⟧′ nil n                              ≡⟨ now->>= ⟩
    (⟦ ω ⟧′ nil n >>= λ v₂ → (ω-nil ∙ v₂) n)  ≡⟨ now->>= ⟩∎
    (ω-nil ∙ ω-nil) n                         ∎

  lemma : ∀ n → ⟦ Ω ⟧′ nil n ⊑ never
  lemma zero    =
    ⟦ Ω ⟧′ nil zero       ≡⟨ reduce-twice zero ⟩⊑
    (ω-nil ∙ ω-nil) zero  ⊑⟨⟩
    never                 ■
  lemma (suc n) =
    ⟦ Ω ⟧′ nil (suc n)  ≡⟨ reduce-twice (suc n) ⟩⊑
    ⟦ Ω ⟧′ nil n        ⊑⟨ lemma n ⟩■
    never               ■

-- A direct proof for Interpreter₂.

Ω-loops₂ : Interpreter₂.⟦ Ω ⟧ nil ≡ never
Ω-loops₂ = antisymmetry (least-upper-bound _ _ lemma) (never⊑ _)
  module Ω-loops₂ where
  open Interpreter₂
  open Trans-⊑
  open Partial

  ω-nil = ƛ (var fzero · var fzero) nil

  reduce-twice :
    ∀ f →
    function eval f (_ , Ω , nil) ≡
    f (_ , var fzero · var fzero , cons ω-nil nil)
  reduce-twice f =
    function eval f (_ , Ω , nil)                   ≡⟨⟩
    function (⟦ Ω ⟧′ nil) f                         ≡⟨ cong {x = function (⟦ Ω ⟧′ nil)}              (_$ f) (⟨ext⟩ λ _ → now->>=) ⟩
    function (⟦ ω ⟧′ nil >>= λ v₂ → ω-nil ∙ v₂) f   ≡⟨ cong {x = function (⟦ ω ⟧′ nil >>= ω-nil ∙_)} (_$ f) (⟨ext⟩ λ _ → now->>=) ⟩
    function (ω-nil ∙ ω-nil) f                      ≡⟨⟩
    f (_ , var fzero · var fzero , cons ω-nil nil)  ∎

  lemma : ∀ n → app→ eval n (_ , Ω , nil) ⊑ never
  lemma zero       = never⊑ never
  lemma (suc zero) =
    app→ eval 1 (_ , Ω , nil)  ≡⟨ reduce-twice _ ⟩⊑
    app→ eval 0 (_ , Ω , nil)  ⊑⟨⟩
    never                      ■
  lemma (suc (suc n)) =
    app→ eval (suc (suc n)) (_ , Ω , nil)  ≡⟨ reduce-twice _ ⟩⊑
    app→ eval (suc n) (_ , Ω , nil)        ⊑⟨ lemma (suc n) ⟩■
    never                                  ■

-- Another proof for Interpreter₂. This proof uses Scott induction.

Ω-loops₂′ : Interpreter₂.⟦ Ω ⟧ nil ≡ never
Ω-loops₂′ = antisymmetry lemma (never⊑ _)
  where
  open Interpreter₂
  open Trans-⊑
  open Partial

  lemma =
    ⟦ Ω ⟧ nil                                              ⊑⟨⟩

    fixP evalP (_ , Ω , nil)                               ≡⟨ cong (_$ (_ , Ω , nil)) $
                                                                fixP-is-fixpoint-combinator evalP ⟩⊑
    function eval (fixP evalP) (_ , Ω , nil)               ⊑⟨ fixP-induction₁
                                                                (λ f → function eval f (_ , Ω , nil) ⊑ never) (
        function eval (const never) (_ , Ω , nil)                  ≡⟨ Ω-loops₂.reduce-twice _ ⟩⊑
        never                                                      ■)
                                                                (λ s hyp →
        function eval (⨆ ∘ s) (_ , Ω , nil)                        ≡⟨ Ω-loops₂.reduce-twice _ ⟩⊑
        ⨆ (s _)                                                    ⊑⟨ least-upper-bound _ _ (λ n →

            s _ [ n ]                                                   ≡⟨ sym $ Ω-loops₂.reduce-twice _ ⟩⊑
            function eval (λ x → s x [ n ]) (_ , Ω , nil)               ⊑⟨ hyp n ⟩■
            never                                                       ■) ⟩

        never                                                      ■)
                                                                evalP
                                                                (λ g hyp →
        function eval (function eval g) (_ , Ω , nil)              ≡⟨ Ω-loops₂.reduce-twice _ ⟩⊑
        function eval g (_ , Ω , nil)                              ⊑⟨ hyp ⟩■
        never                                                      ■) ⟩■

    never                                                  ■

------------------------------------------------------------------------
-- Setup

-- Let us use Interpreter₂ as the default interpreter.

open Interpreter₂ public
