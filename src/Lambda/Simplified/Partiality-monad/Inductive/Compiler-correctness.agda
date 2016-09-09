------------------------------------------------------------------------
-- Compiler correctness
------------------------------------------------------------------------

{-# OPTIONS --without-K --rewriting #-}

module Lambda.Simplified.Partiality-monad.Inductive.Compiler-correctness
  where

open import Equality.Propositional
open import Interval using (ext)
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Monad equality-with-J

open import Partiality-monad.Inductive hiding (_[_])
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

-- Compiler correctness.

mutual

  ⟦⟧-correct :
    ∀ {n} t {ρ : T.Env n} {c s}
      {k : ℕ → T.Value → Maybe C.Value ⊥} {n} →
    (∀ v → steps ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ≳[ n ]
           λ n → k n v) →
    steps ⟨ comp t c , s , comp-env ρ ⟩ ≳[ n ]
    λ n → ⟦ t ⟧′ ρ n >>= k n
  ⟦⟧-correct (var x) {ρ} {c} {s} {k} hyp =
    steps ⟨ var x ∷ c , s , comp-env ρ ⟩                 ≳⟨ step⇓ ⟩
    steps ⟨ c , val (comp-val (ρ x)) ∷ s , comp-env ρ ⟩  ≳⟨ hyp (ρ x) ⟩
    (λ n → k n (ρ x))                                    ≳⟨⟩
    (λ n → ⟦ var x ⟧′ ρ n >>= k n)                       ∎≳

  ⟦⟧-correct (ƛ t) {ρ} {c} {s} {k} hyp =
    steps ⟨ clo (comp t (ret ∷ [])) ∷ c , s , comp-env ρ ⟩   ≳⟨ step⇓ ⟩
    steps ⟨ c , val (comp-val (T.ƛ t ρ)) ∷ s , comp-env ρ ⟩  ≳⟨ hyp (T.ƛ t ρ) ⟩
    (λ n → k n (T.ƛ t ρ))                                    ≳⟨⟩
    (λ n → ⟦ ƛ t ⟧′ ρ n >>= k n)                             ∎≳

  ⟦⟧-correct (t₁ · t₂) {ρ} {c} {s} {k} {n} hyp =
    steps ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩     ≳⟨ (⟦⟧-correct t₁ λ v₁ → ⟦⟧-correct t₂ λ v₂ → ∙-correct v₁ v₂ hyp) ⟩

    (λ n → ⟦ t₁ ⟧′ ρ n >>= λ v₁ →
           ⟦ t₂ ⟧′ ρ n >>= λ v₂ →
           (v₁ ∙ v₂) n >>= k n)                                ≳⟨ cong (λ f → ⟦ t₁ ⟧′ ρ n >>= f)
                                                                       (ext λ v₁ → associativity (⟦ t₂ ⟧′ ρ n) _ _) ⟩≡
    (λ n → ⟦ t₁ ⟧′ ρ n >>= λ v₁ →
           (⟦ t₂ ⟧′ ρ n >>= λ v₂ → (v₁ ∙ v₂) n) >>= k n)       ≳⟨ associativity (⟦ t₁ ⟧′ ρ n) _ _ ⟩≡

    (λ n → ⟦ t₁ · t₂ ⟧′ ρ n >>= k n)                           ∎≳

  ∙-correct :
    ∀ {n} v₁ v₂ {ρ : T.Env n} {c s}
      {k : ℕ → T.Value → Maybe C.Value ⊥} {n} →
    (∀ v → steps ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ≳[ n ]
           λ n → k n v) →
    steps ⟨ app ∷ c
          , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s
          , comp-env ρ
          ⟩ ≳[ n ]
    λ n → (v₁ ∙ v₂) n >>= k n
  ∙-correct (T.ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} {zero} hyp =
    steps ⟨ app ∷ c
          , val (comp-val v₂) ∷ val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
          , comp-env ρ
          ⟩                                                     ≳⟨ refl ⟩≡

    const never                                                 ≳⟨ refl ⟩≡

    (λ n → (T.ƛ t₁ ρ₁ ∙ v₂) n >>= k n)                          ∎≳

  ∙-correct (T.ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} {suc n} hyp = later (
    steps ⟨ app ∷ c
          , val (comp-val v₂) ∷
            val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
          , comp-env ρ
          ⟩ ∘ suc                                          ≳⟨⟩

    steps ⟨ comp t₁ (ret ∷ [])
          , ret c (comp-env ρ) ∷ s
          , snoc (comp-env ρ₁) (comp-val v₂)
          ⟩                                                ≳⟨ (λ n → cong (λ ρ′ → steps ⟨ comp t₁ (ret ∷ []) , ret c (comp-env ρ) ∷ s , ρ′ ⟩ n)
                                                                          (ext [ (λ _ → refl) , (λ _ → refl) ])) ⟩≡∀
    steps ⟨ comp t₁ (ret ∷ [])
          , ret c (comp-env ρ) ∷ s
          , comp-env (snoc ρ₁ v₂)
          ⟩                                                ≳⟨ (⟦⟧-correct t₁ λ v →

        steps ⟨ ret ∷ []
              , val (comp-val v) ∷ ret c (comp-env ρ) ∷ s
              , comp-env (snoc ρ₁ v₂)
              ⟩                                                  ≳⟨ step⇓ ⟩

        steps ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩          ≳⟨ hyp v ⟩

        (λ n → k n v)                                            ≳⟨ step⇓ ⟩

        (λ n → k (suc n) v)                                      ∎≳) ⟩

    (λ n → ⟦ t₁ ⟧′ (snoc ρ₁ v₂) n >>= k (suc n))           ≳⟨⟩

    (λ n → (T.ƛ t₁ ρ₁ ∙ v₂) (suc n) >>= k (suc n))         ∎≳)

-- Note that the equality that is used here is syntactic.

correct :
  ∀ t →
  exec ⟨ comp t [] , [] , empty ⟩ ≡
  (⟦ t ⟧ empty >>= λ v → return (just (comp-val v)))
correct t =
  exec ⟨ comp t [] , [] , empty ⟩                     ≡⟨ cong (λ ρ → exec ⟨ comp t [] , [] , ρ ⟩) (ext λ ()) ⟩
  exec ⟨ comp t [] , [] , comp-env empty ⟩            ≡⟨⟩
  ⨆ (stepsˢ ⟨ comp t [] , [] , comp-env empty ⟩)      ≡⟨ ≳→⨆≡⨆ 0 (⟦⟧-correct t λ v → const (return (just (comp-val v))) ∎≳) ⟩∎
  (⟦ t ⟧ empty >>= λ v → return (just (comp-val v)))  ∎
