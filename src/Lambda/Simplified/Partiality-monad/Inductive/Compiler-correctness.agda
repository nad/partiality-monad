------------------------------------------------------------------------
-- Compiler correctness
------------------------------------------------------------------------

{-# OPTIONS --without-K --rewriting #-}

module Lambda.Simplified.Partiality-monad.Inductive.Compiler-correctness
  where

open import Equality.Propositional
open import Interval using (ext)
open import Prelude hiding (⊥)

open import Monad equality-with-J

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Fixpoints hiding (comp)
open import Partiality-monad.Inductive.Monad
open import Partiality-monad.Inductive.Properties

open import Lambda.Simplified.Compiler
open import Lambda.Simplified.Partiality-monad.Inductive.Interpreter
open import Lambda.Simplified.Partiality-monad.Inductive.Virtual-machine
open import Lambda.Simplified.Syntax
open import Lambda.Simplified.Virtual-machine

private
  module C = Closure Code
  module T = Closure Tm

open Partial
open Trans-⊑

-- Some abbreviations.

evalⁿ : ∀ {n} → Tm n → T.Env n → ℕ → T.Value ⊥
evalⁿ t ρ n = app→ (function eval) n (_ , t , ρ)

_∙ⁿ_ : T.Value → T.Value → ℕ → T.Value ⊥
(v₁ ∙ⁿ v₂) n = function (v₁ ∙ v₂) (app→ (function eval) n)

execⁿ : State → ℕ → Maybe C.Value ⊥
execⁿ s n = app→ (function (transformer execP)) n s

-- Compiler correctness.

mutual

  ⟦⟧-correct :
    ∀ {n} t {ρ : T.Env n} {c s}
      {k : ℕ → T.Value → Maybe C.Value ⊥} {n} →
    (∀ v → execⁿ ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ≳[ n ]
           λ n → k n v) →
    execⁿ ⟨ comp t c , s , comp-env ρ ⟩ ≳[ n ]
    λ n → evalⁿ t ρ (suc n) >>= k n
  ⟦⟧-correct (var x) {ρ} {c} {s} {k} hyp =
    execⁿ ⟨ var x ∷ c , s , comp-env ρ ⟩                 ≳⟨ step⇓ ⟩
    execⁿ ⟨ c , val (comp-val (ρ x)) ∷ s , comp-env ρ ⟩  ≳⟨ hyp (ρ x) ⟩
    (λ n → k n (ρ x))                                    ≳⟨⟩
    (λ n → evalⁿ (var x) ρ (suc n) >>= k n)              ∎≳

  ⟦⟧-correct (ƛ t) {ρ} {c} {s} {k} hyp =
    execⁿ ⟨ clo (comp t (ret ∷ [])) ∷ c , s , comp-env ρ ⟩   ≳⟨ step⇓ ⟩
    execⁿ ⟨ c , val (comp-val (T.ƛ t ρ)) ∷ s , comp-env ρ ⟩  ≳⟨ hyp (T.ƛ t ρ) ⟩
    (λ n → k n (T.ƛ t ρ))                                    ≳⟨⟩
    (λ n → evalⁿ (ƛ t) ρ (suc n) >>= k n)                    ∎≳

  ⟦⟧-correct (t₁ · t₂) {ρ} {c} {s} {k} {n} hyp =
    execⁿ ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩    ≳⟨ (⟦⟧-correct t₁ λ v₁ → ⟦⟧-correct t₂ λ v₂ → ∙-correct v₁ v₂ hyp) ⟩

    (λ n → evalⁿ t₁ ρ (suc n) >>=′ λ v₁ →
           evalⁿ t₂ ρ (suc n) >>=′ λ v₂ →
           (v₁ ∙ⁿ v₂) n >>=
           k n)                                               ≳⟨ cong (evalⁿ t₁ ρ (suc n) >>=′_)
                                                                      (ext λ _ → associativity (evalⁿ t₂ ρ (suc n)) _ _) ⟩≡
    (λ n → evalⁿ t₁ ρ (suc n) >>=′ λ v₁ →
           (evalⁿ t₂ ρ (suc n) >>=′ λ v₂ → (v₁ ∙ⁿ v₂) n) >>=
           k n)                                               ≳⟨ associativity (evalⁿ t₁ ρ (suc n)) _ _ ⟩≡

    (λ n → evalⁿ (t₁ · t₂) ρ (suc n) >>= k n)                 ∎≳

  ∙-correct :
    ∀ {n} v₁ v₂ {ρ : T.Env n} {c s}
      {k : ℕ → T.Value → Maybe C.Value ⊥} {n} →
    (∀ v → execⁿ ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ≳[ n ]
           λ n → k n v) →
    execⁿ ⟨ app ∷ c
          , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s
          , comp-env ρ
          ⟩ ≳[ n ]
    λ n → (v₁ ∙ⁿ v₂) n >>= k n

  ∙-correct (T.ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} {zero} hyp =
    execⁿ ⟨ app ∷ c
          , val (comp-val v₂) ∷ val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
          , comp-env ρ
          ⟩                                                     ≳⟨ refl ⟩≡

    const never                                                 ≳⟨ refl ⟩≡

    (λ n → (T.ƛ t₁ ρ₁ ∙ⁿ v₂) n >>= k n)                         ∎≳

  ∙-correct (T.ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} {suc n} hyp = later (
    execⁿ ⟨ app ∷ c
          , val (comp-val v₂) ∷ val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
          , comp-env ρ
          ⟩ ∘ suc                                               ≳⟨⟩

    execⁿ ⟨ comp t₁ (ret ∷ [])
          , ret c (comp-env ρ) ∷ s
          , snoc (comp-env ρ₁) (comp-val v₂)
          ⟩                                                     ≳⟨ (λ n → cong (λ ρ′ → execⁿ ⟨ comp t₁ (ret ∷ []) , ret c (comp-env ρ) ∷ s , ρ′ ⟩ n)
                                                                               (sym comp-snoc)) ⟩≡∀
    execⁿ ⟨ comp t₁ (ret ∷ [])
          , ret c (comp-env ρ) ∷ s
          , comp-env (snoc ρ₁ v₂)
          ⟩                                                     ≳⟨ (⟦⟧-correct t₁ λ v →

        execⁿ ⟨ ret ∷ []
              , val (comp-val v) ∷ ret c (comp-env ρ) ∷ s
              , comp-env (snoc ρ₁ v₂)
              ⟩                                                       ≳⟨ step⇓ ⟩

        execⁿ ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩               ≳⟨ hyp v ⟩

        (λ n → k n v)                                                 ≳⟨ step⇓ ⟩

        (λ n → k (suc n) v)                                           ∎≳) ⟩

    (λ n → evalⁿ t₁ (snoc ρ₁ v₂) (suc n) >>= k (suc n))         ≳⟨⟩

    (λ n → (T.ƛ t₁ ρ₁ ∙ⁿ v₂) (suc n) >>= k (suc n))             ∎≳)

-- Note that the equality that is used here is syntactic.

correct :
  ∀ t →
  exec ⟨ comp t [] , [] , empty ⟩ ≡
  (⟦ t ⟧ empty >>= λ v → return (just (comp-val v)))
correct t =
  exec ⟨ comp t [] , [] , empty ⟩                            ≡⟨ cong (λ ρ → exec ⟨ comp t [] , [] , ρ ⟩) $ sym comp-empty ⟩

  exec ⟨ comp t [] , [] , comp-env empty ⟩                   ≡⟨⟩

  ⨆ ( execⁿ ⟨ comp t [] , [] , comp-env empty ⟩
    , _
    )                                                        ≡⟨ ≳→⨆≡⨆ 1 (⟦⟧-correct t $ λ v →

      execⁿ ⟨ [] , val (comp-val v) ∷ [] , comp-env empty ⟩       ≳⟨ step⇓ ⟩
      const (return (just (comp-val v)))                          ∎≳) ⟩

  ⨆ ( (λ n → evalⁿ t empty n >>= λ v →
             return (just (comp-val v)))
    , _
    )                                                        ≡⟨⟩

  (⟦ t ⟧ empty >>= λ v → return (just (comp-val v)))         ∎
