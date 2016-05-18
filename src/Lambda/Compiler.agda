------------------------------------------------------------------------
-- A correct compiler
------------------------------------------------------------------------

{-# OPTIONS --without-K --rewriting #-}

module Lambda.Compiler where

open import Equality.Propositional
open import Interval using (ext)
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J hiding (id; _∘_)
open import Maybe equality-with-J as Maybe
open import Monad equality-with-J
open import Nat equality-with-J as Nat

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Monad
open import Partiality-monad.Inductive.Properties

open import Lambda.Interpreter
open import Lambda.Syntax hiding ([_])
open import Lambda.Virtual-machine

private
  module C = Closure Code
  module T = Closure Tm

------------------------------------------------------------------------
-- Compiler

-- The compiler takes a code continuation.

comp : ∀ {n} → Tm n → Code n → Code n
comp (con i)   c = con i ∷ c
comp (var x)   c = var x ∷ c
comp (ƛ t)     c = clo (comp t (ret ∷ [])) ∷ c
comp (t₁ · t₂) c = comp t₁ (comp t₂ (app ∷ c))

-- Environments and values can also be compiled.

mutual

  comp-env : ∀ {n} → T.Env n → C.Env n
  comp-env ρ n = comp-val (ρ n)

  comp-val : T.Value → C.Value
  comp-val (T.con i) = C.con i
  comp-val (T.ƛ t ρ) = C.ƛ (comp t (ret ∷ [])) (comp-env ρ)

------------------------------------------------------------------------
-- Compiler correctness

mutual

  -- TODO: The proof is not structurally recursive. The framework
  -- involving _≈_ hides the natural numbers.

  {-# NON_TERMINATING #-}

  ⟦⟧-correct :
    ∀ {n} t {ρ : T.Env n} {c s}
      {k : T.Value → Increasing-sequence (Maybe C.Value)} →
    (∀ v → stepsˢ ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ≈ k v) →
    stepsˢ ⟨ comp t c , s , comp-env ρ ⟩ ≈ ⟦ t ⟧ˢ ρ >>=ˢ k
  ⟦⟧-correct (con i) {ρ} {c} {s} {k} hyp =
    stepsˢ ⟨ con i ∷ c , s , comp-env ρ ⟩                     ≈⟨ step⇓ ⟩
    stepsˢ ⟨ c , val (comp-val (T.con i)) ∷ s , comp-env ρ ⟩  ≈⟨ hyp (T.con i) ⟩
    k (T.con i)                                               ≡⟨ (λ _ → refl) ⟩≈
    ⟦ con i ⟧ˢ ρ >>=ˢ k                                       ∎≈

  ⟦⟧-correct (var x) {ρ} {c} {s} {k} hyp =
    stepsˢ ⟨ var x ∷ c , s , comp-env ρ ⟩                 ≈⟨ step⇓ ⟩
    stepsˢ ⟨ c , val (comp-val (ρ x)) ∷ s , comp-env ρ ⟩  ≈⟨ hyp (ρ x) ⟩
    k (ρ x)                                               ≡⟨ (λ _ → refl) ⟩≈
    ⟦ var x ⟧ˢ ρ >>=ˢ k                                   ∎≈

  ⟦⟧-correct (ƛ t) {ρ} {c} {s} {k} hyp =
    stepsˢ ⟨ clo (comp t (ret ∷ [])) ∷ c , s , comp-env ρ ⟩   ≈⟨ step⇓ ⟩
    stepsˢ ⟨ c , val (comp-val (T.ƛ t ρ)) ∷ s , comp-env ρ ⟩  ≈⟨ hyp (T.ƛ t ρ) ⟩
    k (T.ƛ t ρ)                                               ≡⟨ (λ _ → refl) ⟩≈
    ⟦ ƛ t ⟧ˢ ρ >>=ˢ k                                         ∎≈

  ⟦⟧-correct (t₁ · t₂) {ρ} {c} {s} {k} hyp =
    stepsˢ ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩          ≈⟨ ⟦⟧-correct t₁ (λ v₁ → ⟦⟧-correct t₂ (λ v₂ → ∙-correct v₁ v₂ hyp)) ⟩

    (⟦ t₁ ⟧ˢ ρ >>=ˢ λ v₁ → ⟦ t₂ ⟧ˢ ρ >>=ˢ λ v₂ → v₁ ∙ˢ v₂ >>=ˢ k)    ≡⟨ (λ n → cong (λ f → run (⟦ t₁ ⟧′ ρ n >>= f))
                                                                                    (ext λ v₁ → Monad.associativity tr (⟦ t₂ ⟧′ ρ n) _ _)) ⟩≈

    (⟦ t₁ ⟧ˢ ρ >>=ˢ λ v₁ → (⟦ t₂ ⟧ˢ ρ >>=ˢ λ v₂ → v₁ ∙ˢ v₂) >>=ˢ k)  ≡⟨ (λ n → cong MaybeT.run $ Monad.associativity tr (⟦ t₁ ⟧′ ρ n) _ _) ⟩≈

    ⟦ t₁ · t₂ ⟧ˢ ρ >>=ˢ k                                            ∎≈
    where
    tr = Monad-transformer.transform (Maybe.monad-transformer ext)

  ∙-correct :
    ∀ {n} v₁ v₂ {ρ : T.Env n} {c s}
      {k : T.Value → Increasing-sequence (Maybe C.Value)} →
    (∀ v → stepsˢ ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ≈ k v) →
    stepsˢ ⟨ app ∷ c
           , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s
           , comp-env ρ
           ⟩ ≈
    v₁ ∙ˢ v₂ >>=ˢ k
  ∙-correct (T.con i) v₂ hyp =
    constˢ (run fail) ∎≈

  ∙-correct (T.ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} hyp =
    stepsˢ ⟨ app ∷ c
           , val (comp-val v₂) ∷
             val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
           , comp-env ρ
           ⟩                                                ≈⟨ step⇓ ⟩

    stepsˢ ⟨ comp t₁ (ret ∷ [])
           , ret c (comp-env ρ) ∷ s
           , snoc (comp-env ρ₁) (comp-val v₂)
           ⟩                                                ≡⟨ (λ n → cong (λ ρ′ → steps ⟨ comp t₁ (ret ∷ []) , ret c (comp-env ρ) ∷ s , ρ′ ⟩ n)
                                                                           (ext (maybe (λ _ → refl) refl))) ⟩≈
    stepsˢ ⟨ comp t₁ (ret ∷ [])
           , ret c (comp-env ρ) ∷ s
           , comp-env (snoc ρ₁ v₂)
           ⟩                                                ≈⟨ ⟦⟧-correct t₁ (λ v →

        stepsˢ ⟨ ret ∷ []
               , val (comp-val v) ∷ ret c (comp-env ρ) ∷ s
               , comp-env (snoc ρ₁ v₂)
               ⟩                                                 ≈⟨ step⇓ ⟩

        stepsˢ ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩         ≈⟨ hyp v ⟩

        k v                                                      ≈⟨ step⇓ ⟩

        tailˢ (k v)                                              ∎≈ ) ⟩

    ⟦ t₁ ⟧ˢ (snoc ρ₁ v₂) >>=ˢ tailˢ ∘ k                     ≈⟨ step⇑ ⟩

    T.ƛ t₁ ρ₁ ∙ˢ v₂ >>=ˢ k                                  ∎≈

-- Note that the equality that is used here is syntactic.

correct :
  ∀ t →
  wrap (exec ⟨ comp t [] , [] , empty ⟩) ≡
  (⟦ t ⟧ empty >>= λ v → return (comp-val v))
correct t =
  wrap (exec ⟨ comp t [] , [] , empty ⟩)                 ≡⟨ cong (λ ρ → wrap (exec ⟨ comp t [] , [] , ρ ⟩)) (ext λ ()) ⟩

  wrap (exec ⟨ comp t [] , [] , comp-env empty ⟩)        ≡⟨⟩

  wrap (⨆ (stepsˢ ⟨ comp t [] , [] , comp-env empty ⟩))  ≡⟨ cong wrap (≈→⨆≡⨆ (⟦⟧-correct t λ v →
                                                              constˢ (MaybeT.run (return (comp-val v))) ∎≈)) ⟩
  wrap (⨆ (⟦ t ⟧ˢ empty >>=ˢ λ v →
           constˢ (MaybeT.run (return (comp-val v)))))   ≡⟨ cong (λ s → wrap (⨆ s))
                                                                 (_↔_.to equality-characterisation-increasing (λ _ → refl)) ⟩∎
  (⟦ t ⟧ empty >>= λ v → return (comp-val v))            ∎
