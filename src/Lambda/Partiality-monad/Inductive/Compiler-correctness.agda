------------------------------------------------------------------------
-- Compiler correctness
------------------------------------------------------------------------

{-# OPTIONS --cubical #-}

module Lambda.Partiality-monad.Inductive.Compiler-correctness where

open import Equality.Propositional
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms equality-with-J
  using (ext; ⟨ext⟩)
open import Maybe equality-with-J as Maybe
open import Monad equality-with-J

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Monad

open import Lambda.Compiler
open import Lambda.Partiality-monad.Inductive.Interpreter
open import Lambda.Partiality-monad.Inductive.Virtual-machine
open import Lambda.Syntax
open import Lambda.Virtual-machine

private
  module C = Closure Code
  module T = Closure Tm

-- Compiler correctness.

mutual

  ⟦⟧-correct :
    ∀ {n} t {ρ : T.Env n} {c s} {k : ℕ → T.Value → M C.Value} {n} →
    (∀ v → steps ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ≳[ n ]
           λ n → run (k n v)) →
    steps ⟨ comp t c , s , comp-env ρ ⟩ ≳[ n ]
    λ n → run (⟦ t ⟧′ ρ n >>= k n)
  ⟦⟧-correct (con i) {ρ} {c} {s} {k} hyp =
    steps ⟨ con i ∷ c , s , comp-env ρ ⟩                     ≳⟨ step⇓ ⟩
    steps ⟨ c , val (comp-val (T.con i)) ∷ s , comp-env ρ ⟩  ≳⟨ hyp (T.con i) ⟩
    (λ n → run (k n (T.con i)))                              ≡⟨ sym now->>= ⟩≳
    (λ n → run (⟦ con i ⟧′ ρ n >>= k n))                     ∎≳

  ⟦⟧-correct (var x) {ρ} {c} {s} {k} hyp =
    steps ⟨ var x ∷ c , s , comp-env ρ ⟩                 ≳⟨ step⇓ ⟩
    steps ⟨ c , val (comp-val (ρ x)) ∷ s , comp-env ρ ⟩  ≳⟨ hyp (ρ x) ⟩
    (λ n → run (k n (ρ x)))                              ≡⟨ sym now->>= ⟩≳
    (λ n → run (⟦ var x ⟧′ ρ n >>= k n))                 ∎≳

  ⟦⟧-correct (ƛ t) {ρ} {c} {s} {k} hyp =
    steps ⟨ clo (comp t (ret ∷ [])) ∷ c , s , comp-env ρ ⟩   ≳⟨ step⇓ ⟩
    steps ⟨ c , val (comp-val (T.ƛ t ρ)) ∷ s , comp-env ρ ⟩  ≳⟨ hyp (T.ƛ t ρ) ⟩
    (λ n → run (k n (T.ƛ t ρ)))                              ≡⟨ sym now->>= ⟩≳
    (λ n → run (⟦ ƛ t ⟧′ ρ n >>= k n))                       ∎≳

  ⟦⟧-correct (t₁ · t₂) {ρ} {c} {s} {k} {n} hyp =
    steps ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩     ≳⟨ (⟦⟧-correct t₁ {n = n} λ v₁ → ⟦⟧-correct t₂ λ v₂ → ∙-correct v₁ v₂ hyp) ⟩

    (λ n → run (⟦ t₁ ⟧′ ρ n >>= λ v₁ →
                ⟦ t₂ ⟧′ ρ n >>= λ v₂ →
                (v₁ ∙ v₂) n >>= k n))                          ≡⟨ cong (λ f → run (⟦ t₁ ⟧′ ρ n >>= f))
                                                                       (⟨ext⟩ λ v₁ → Monad.associativity tr (⟦ t₂ ⟧′ ρ n) _ _) ⟩≳
    (λ n → run (⟦ t₁ ⟧′ ρ n >>= λ v₁ →
               (⟦ t₂ ⟧′ ρ n >>= λ v₂ → (v₁ ∙ v₂) n) >>= k n))  ≡⟨ cong MaybeT.run $ Monad.associativity tr (⟦ t₁ ⟧′ ρ n) _ _ ⟩≳

    (λ n → run (⟦ t₁ · t₂ ⟧′ ρ n >>= k n))                     ∎≳
    where
    tr = Monad-transformer.transform (Maybe.monad-transformer ext)

  ∙-correct :
    ∀ {n} v₁ v₂ {ρ : T.Env n} {c s} {k : ℕ → T.Value → M C.Value} {n} →
    (∀ v → steps ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ≳[ n ]
           λ n → run (k n v)) →
    steps ⟨ app ∷ c
          , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s
          , comp-env ρ
          ⟩ ≳[ n ]
    λ n → run ((v₁ ∙ v₂) n >>= k n)
  ∙-correct (T.con i) v₂ {ρ} {c} {s} {k} hyp =
    steps ⟨ app ∷ c
          , val (comp-val v₂) ∷ val (C.con i) ∷ s
          , comp-env ρ
          ⟩                                        ≳⟨⟩

    const (run fail)                               ≡⟨ sym now->>= ⟩≳

    (λ n → run ((T.con i ∙ v₂) n >>= k n))         ∎≳

  ∙-correct (T.ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} {zero} hyp =
    steps ⟨ app ∷ c
          , val (comp-val v₂) ∷ val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
          , comp-env ρ
          ⟩                                   ≡⟨ refl ⟩≳

    const never                               ≡⟨ sym never->>= ⟩≳

    const (never >>= _)                       ≡⟨ cong (_>>= maybe (MaybeT.run ∘ k 0) (return nothing) ⦂ (_ ⊥ → _)) (sym never->>=) ⟩≳

    (λ n → run ((T.ƛ t₁ ρ₁ ∙ v₂) n >>= k n))  ∎≳

  ∙-correct (T.ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} {suc n} hyp = later (
    steps ⟨ app ∷ c
          , val (comp-val v₂) ∷
            val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
          , comp-env ρ
          ⟩ ∘ suc                                         ≳⟨⟩

    steps ⟨ comp t₁ (ret ∷ [])
          , ret c (comp-env ρ) ∷ s
          , snoc (comp-env ρ₁) (comp-val v₂)
          ⟩                                               ∀≡⟨ (λ n → cong (λ ρ′ → steps ⟨ comp t₁ (ret ∷ []) , ret c (comp-env ρ) ∷ s , ρ′ ⟩ n) $
                                                                          sym comp-snoc) ⟩≳
    steps ⟨ comp t₁ (ret ∷ [])
          , ret c (comp-env ρ) ∷ s
          , comp-env (snoc ρ₁ v₂)
          ⟩                                               ≳⟨ (⟦⟧-correct t₁ {n = n} λ v →

        steps ⟨ ret ∷ []
              , val (comp-val v) ∷ ret c (comp-env ρ) ∷ s
              , comp-env (snoc ρ₁ v₂)
              ⟩                                                ≳⟨ step⇓ ⟩

        steps ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩        ≳⟨ hyp v ⟩

        (λ n → run (k n v))                                    ≳⟨ step⇓ ⟩

        (λ n → run (k (suc n) v))                              ∎≳) ⟩

    (λ n → run (⟦ t₁ ⟧′ (snoc ρ₁ v₂) n >>= k (suc n)))    ≳⟨⟩

    (λ n → run ((T.ƛ t₁ ρ₁ ∙ v₂) (suc n) >>= k (suc n)))  ∎≳)

-- Note that the equality that is used here is syntactic.

correct :
  ∀ t →
  wrap (exec ⟨ comp t [] , [] , empty ⟩) ≡
  (⟦ t ⟧ empty >>= λ v → return (comp-val v))
correct t =
  wrap (exec ⟨ comp t [] , [] , empty ⟩)                   ≡⟨ cong (λ ρ → wrap (exec ⟨ comp t [] , [] , ρ ⟩)) $ sym comp-empty ⟩

  wrap (exec ⟨ comp t [] , [] , comp-env empty ⟩)          ≡⟨⟩

  wrap (⨆ (stepsˢ ⟨ comp t [] , [] , comp-env empty ⟩))    ≡⟨ cong wrap (≳→⨆≡⨆ 0 $ ⟦⟧-correct t λ v →
                                                                                     const (MaybeT.run (return (comp-val v))) ∎≳) ⟩
  wrap (⨆ (⟦ t ⟧ˢ empty >>=ˢ λ v →
           constˢ (MaybeT.run (return (comp-val v)))))     ≡⟨ cong (λ s → wrap (⨆ s))
                                                                   (_↔_.to equality-characterisation-increasing (λ _ → refl)) ⟩
  wrap (⨆ (maybe (λ v → MaybeT.run (return (comp-val v)))
                 (return nothing)
             ∗-inc
           ⟦ t ⟧ˢ empty))                                  ≡⟨ cong wrap (sym ⨆->>=) ⟩∎

  (⟦ t ⟧ empty >>= λ v → return (comp-val v))              ∎
