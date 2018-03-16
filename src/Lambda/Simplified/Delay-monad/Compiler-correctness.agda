------------------------------------------------------------------------
-- Compiler correctness
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Lambda.Simplified.Delay-monad.Compiler-correctness where

import Equality.Propositional as E
open import Prelude

open import Monad E.equality-with-J

open import Delay-monad
open import Delay-monad.Bisimilarity
open import Delay-monad.Monad

open import Lambda.Simplified.Compiler
open import Lambda.Simplified.Delay-monad.Interpreter
open import Lambda.Simplified.Delay-monad.Virtual-machine
open import Lambda.Simplified.Syntax
open import Lambda.Simplified.Virtual-machine

private
  module C = Closure Code
  module T = Closure Tm

-- Compiler correctness.

mutual

  ⟦⟧-correct :
    ∀ {i n} t {ρ : T.Env n} {c s}
      {k : T.Value → Delay (Maybe C.Value) ∞} →
    (∀ v → [ i ] exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ≈ k v) →
    [ i ] exec ⟨ comp t c , s , comp-env ρ ⟩ ≈ ⟦ t ⟧ ρ >>= k

  ⟦⟧-correct (var x) {ρ} {c} {s} {k} hyp =
    exec ⟨ var x ∷ c , s , comp-env ρ ⟩                 ≳⟨⟩
    exec ⟨ c , val (comp-val (ρ x)) ∷ s , comp-env ρ ⟩  ≈⟨ hyp (ρ x) ⟩∼
    k (ρ x)                                             ∼⟨⟩
    ⟦ var x ⟧ ρ >>= k                                   ∎

  ⟦⟧-correct (ƛ t) {ρ} {c} {s} {k} hyp =
    exec ⟨ clo (comp t (ret ∷ [])) ∷ c , s , comp-env ρ ⟩   ≳⟨⟩
    exec ⟨ c , val (comp-val (T.ƛ t ρ)) ∷ s , comp-env ρ ⟩  ≈⟨ hyp (T.ƛ t ρ) ⟩∼
    k (T.ƛ t ρ)                                             ∼⟨⟩
    ⟦ ƛ t ⟧ ρ >>= k                                         ∎

  ⟦⟧-correct (t₁ · t₂) {ρ} {c} {s} {k} hyp =
    exec ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩      ≈⟨ (⟦⟧-correct t₁ λ v₁ → ⟦⟧-correct t₂ λ v₂ → ∙-correct v₁ v₂ hyp) ⟩∼

    (⟦ t₁ ⟧ ρ >>= λ v₁ → ⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂ >>= k)    ∼⟨ (⟦ t₁ ⟧ ρ ∎) >>=-cong (λ _ → associativity′ (⟦ t₂ ⟧ ρ) _ _) ⟩

    (⟦ t₁ ⟧ ρ >>= λ v₁ → (⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂) >>= k)  ∼⟨ associativity′ (⟦ t₁ ⟧ ρ) _ _ ⟩

    ⟦ t₁ · t₂ ⟧ ρ >>= k                                        ∎

  ∙-correct :
    ∀ {i n} v₁ v₂ {ρ : T.Env n} {c s}
      {k : T.Value → Delay (Maybe C.Value) ∞} →
    (∀ v → [ i ] exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ≈ k v) →
    [ i ] exec ⟨ app ∷ c
               , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s
               , comp-env ρ
               ⟩ ≈
          v₁ ∙ v₂ >>= k
  ∙-correct (T.ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} hyp =
    exec ⟨ app ∷ c
         , val (comp-val v₂) ∷ val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
         , comp-env ρ
         ⟩                                                     ≈⟨ later (λ { .force →

      exec ⟨ comp t₁ (ret ∷ [])
           , ret c (comp-env ρ) ∷ s
           , snoc (comp-env ρ₁) (comp-val v₂)
           ⟩                                                        ≡⟨ E.cong (λ ρ′ →
                                                                                 exec ⟨ comp t₁ (ret ∷ []) , ret c (comp-env ρ) ∷ s , ρ′ ⟩) $
                                                                              E.sym comp-snoc ⟩
      exec ⟨ comp t₁ (ret ∷ [])
           , ret c (comp-env ρ) ∷ s
           , comp-env (snoc ρ₁ v₂)
           ⟩                                                        ≈⟨ ⟦⟧-correct t₁ (λ v →

        exec ⟨ ret ∷ []
             , val (comp-val v) ∷ ret c (comp-env ρ) ∷ s
             , comp-env (snoc ρ₁ v₂)
             ⟩                                                           ≳⟨⟩

        exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩                   ≈⟨ hyp v ⟩∎

        k v                                                              ∎) ⟩∼

      ⟦ t₁ ⟧ (snoc ρ₁ v₂) >>= k                                     ∎ }) ⟩∎

    T.ƛ t₁ ρ₁ ∙ v₂ >>= k                                       ∎

-- Note that the equality that is used here is syntactic.

correct :
  ∀ t →
  exec ⟨ comp t [] , [] , empty ⟩ ≈
  ⟦ t ⟧ empty >>= λ v → return (just (comp-val v))
correct t =
  exec ⟨ comp t [] , [] , empty ⟩                     ≡⟨ E.cong (λ ρ → exec ⟨ comp t [] , [] , ρ ⟩) $ E.sym comp-empty ⟩
  exec ⟨ comp t [] , [] , comp-env empty ⟩            ≈⟨ ⟦⟧-correct t (λ v → return (just (comp-val v)) ∎) ⟩
  (⟦ t ⟧ empty >>= λ v → return (just (comp-val v)))  ∎
