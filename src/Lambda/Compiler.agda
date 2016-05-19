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

-- TODO: Can ⟦⟧-correct-⊑ and ⟦⟧-correct-⊒ be merged into a single
-- proof with less code duplication?

mutual

  ⟦⟧-correct-⊑ :
    ∀ {n} t {ρ : T.Env n} {c s} {k : T.Value → MaybeT _⊥ C.Value} n →
    (∀ v → steps ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ n ⊑
           run (k v)) →
    steps ⟨ comp t c , s , comp-env ρ ⟩ n ⊑ run (⟦ t ⟧′ ρ n >>= k)
  ⟦⟧-correct-⊑ (con i) {ρ} {c} {s} {k} n hyp =
    steps ⟨ con i ∷ c , s , comp-env ρ ⟩ n                     ⊑⟨ steps-increasing ⟨ con _ ∷ _ , _ , _ ⟩ n ⟩
    steps ⟨ con i ∷ c , s , comp-env ρ ⟩ (1 + n)               ⊑⟨⟩
    steps ⟨ c , val (comp-val (T.con i)) ∷ s , comp-env ρ ⟩ n  ⊑⟨ hyp (T.con i) ⟩
    run (k (T.con i))                                          ⊑⟨⟩
    run (⟦ con i ⟧′ ρ n >>= k)                                 ■

  ⟦⟧-correct-⊑ (var x) {ρ} {c} {s} {k} n hyp =
    steps ⟨ var x ∷ c , s , comp-env ρ ⟩ n                 ⊑⟨ steps-increasing ⟨ var _ ∷ _ , _ , _ ⟩ n ⟩
    steps ⟨ var x ∷ c , s , comp-env ρ ⟩ (suc n)           ⊑⟨⟩
    steps ⟨ c , val (comp-val (ρ x)) ∷ s , comp-env ρ ⟩ n  ⊑⟨ hyp (ρ x) ⟩
    run (k (ρ x))                                          ⊑⟨⟩
    run (⟦ var x ⟧′ ρ n >>= k)                             ■

  ⟦⟧-correct-⊑ (ƛ t) {ρ} {c} {s} {k} n hyp =
    steps ⟨ clo (comp t (ret ∷ [])) ∷ c , s , comp-env ρ ⟩ n        ⊑⟨ steps-increasing ⟨ clo _ ∷ _ , _ , _ ⟩ n ⟩
    steps ⟨ clo (comp t (ret ∷ [])) ∷ c , s , comp-env ρ ⟩ (suc n)  ⊑⟨⟩
    steps ⟨ c , val (comp-val (T.ƛ t ρ)) ∷ s , comp-env ρ ⟩ n       ⊑⟨ hyp (T.ƛ t ρ) ⟩
    run (k (T.ƛ t ρ))                                               ⊑⟨⟩
    run (⟦ ƛ t ⟧′ ρ n >>= k)                                        ■

  ⟦⟧-correct-⊑ (t₁ · t₂) {ρ} {c} {s} {k} n hyp =
    steps ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩ n  ⊑⟨ ⟦⟧-correct-⊑ t₁ n (λ v₁ → ⟦⟧-correct-⊑ t₂ n (λ v₂ → ∙-correct-⊑ v₁ v₂ n hyp)) ⟩

    run (⟦ t₁ ⟧′ ρ n >>= λ v₁ →
         ⟦ t₂ ⟧′ ρ n >>= λ v₂ →
         (v₁ ∙ v₂) n >>= k)                                   ⊑⟨ (cong (λ f → run (⟦ t₁ ⟧′ ρ n >>= f))
                                                                       (ext λ v₁ → Monad.associativity tr (⟦ t₂ ⟧′ ρ n) _ _)) ⟩≡
    run (⟦ t₁ ⟧′ ρ n >>= λ v₁ →
         (⟦ t₂ ⟧′ ρ n >>= λ v₂ → (v₁ ∙ v₂) n) >>= k)          ⊑⟨ (cong MaybeT.run $ Monad.associativity tr (⟦ t₁ ⟧′ ρ n) _ _) ⟩≡

    run (⟦ t₁ · t₂ ⟧′ ρ n >>= k)                              ■
    where
    tr = Monad-transformer.transform (Maybe.monad-transformer ext)

  ∙-correct-⊑ :
    ∀ {n} v₁ v₂ {ρ : T.Env n} {c s} {k : T.Value → M C.Value} n →
    (∀ v → steps ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ n ⊑
           run (k v)) →
    steps ⟨ app ∷ c
          , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s
          , comp-env ρ
          ⟩ n ⊑
    run ((v₁ ∙ v₂) n >>= k)

  ∙-correct-⊑ (T.con i) v₂ {ρ} {c} {s} {k} n hyp =
    steps ⟨ app ∷ c
          , val (comp-val v₂) ∷ val (C.con i) ∷ s
          , comp-env ρ
          ⟩ n                                      ⊑⟨⟩
    run fail                                       ⊑⟨⟩
    run ((T.con i ∙ v₂) n >>= k)                   ■

  ∙-correct-⊑ (T.ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} zero hyp =
    steps ⟨ app ∷ c
          , val (comp-val v₂) ∷ val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
          , comp-env ρ
          ⟩ 0                                                   ⊑⟨⟩
    never                                                       ⊑⟨⟩
    run ((T.ƛ t₁ ρ₁ ∙ v₂) 0 >>= k)                              ■

  ∙-correct-⊑ (T.ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} (suc n) hyp =
    steps ⟨ app ∷ c
          , val (comp-val v₂) ∷
            val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
          , comp-env ρ
          ⟩ (suc n)                                            ⊑⟨⟩

    steps ⟨ comp t₁ (ret ∷ [])
          , ret c (comp-env ρ) ∷ s
          , snoc (comp-env ρ₁) (comp-val v₂)
          ⟩ n                                                  ⊑⟨ cong (λ ρ′ → steps ⟨ comp t₁ (ret ∷ []) , ret c (comp-env ρ) ∷ s , ρ′ ⟩ n)
                                                                       (ext (maybe (λ _ → refl) refl)) ⟩≡
    steps ⟨ comp t₁ (ret ∷ [])
          , ret c (comp-env ρ) ∷ s
          , comp-env (snoc ρ₁ v₂)
          ⟩ n                                                  ⊑⟨ ⟦⟧-correct-⊑ t₁ n (λ v →

        steps ⟨ ret ∷ []
              , val (comp-val v) ∷ ret c (comp-env ρ) ∷ s
              , comp-env (snoc ρ₁ v₂)
              ⟩ n                                                   ⊑⟨ steps-increasing ⟨ ret ∷ [] , val _ ∷ ret _ _ ∷ _
                                                                                                   , comp-env (snoc ρ₁ v₂) ⟩ n ⟩
        steps ⟨ ret ∷ []
              , val (comp-val v) ∷ ret c (comp-env ρ) ∷ s
              , comp-env (snoc ρ₁ v₂)
              ⟩ (suc n)                                             ⊑⟨⟩

        steps ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ n           ⊑⟨ steps-increasing ⟨ c , _ , _ ⟩ n ⟩

        steps ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ (suc n)     ⊑⟨ hyp v ⟩■

        run (k v)                                                   ■) ⟩

    run (⟦ t₁ ⟧′ (snoc ρ₁ v₂) n >>= k)                         ⊑⟨⟩

    run ((T.ƛ t₁ ρ₁ ∙ v₂) (suc n) >>= k)                       ■

mutual

  ⟦⟧-correct-⊒ :
    ∀ {n} t {ρ : T.Env n} {c s} {k : T.Value → MaybeT _⊥ C.Value} n →
    (∀ v → ∃ λ m →
       steps ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ (m + n) ⊒
       run (k v)) →
    ∃ λ m → steps ⟨ comp t c , s , comp-env ρ ⟩ (m + n) ⊒
            run (⟦ t ⟧′ ρ n >>= k)
  ⟦⟧-correct-⊒ (con i) {ρ} {c} {s} {k} n hyp =
    let m , h = hyp (T.con i) in
      1 + m
    , (run (⟦ con i ⟧′ ρ n >>= k)                                       ⊑⟨⟩
       run (k (T.con i))                                                ⊑⟨ h ⟩
       steps ⟨ c , val (comp-val (T.con i)) ∷ s , comp-env ρ ⟩ (m + n)  ⊑⟨⟩
       steps ⟨ con i ∷ c , s , comp-env ρ ⟩ (1 + m + n)                 ■)

  ⟦⟧-correct-⊒ (var x) {ρ} {c} {s} {k} n hyp =
    let m , h = hyp (ρ x) in
      1 + m
    , (run (⟦ var x ⟧′ ρ n >>= k)                                   ⊑⟨⟩
       run (k (ρ x))                                                ⊑⟨ h ⟩
       steps ⟨ c , val (comp-val (ρ x)) ∷ s , comp-env ρ ⟩ (m + n)  ⊑⟨⟩
       steps ⟨ var x ∷ c , s , comp-env ρ ⟩ (1 + m + n)             ■)

  ⟦⟧-correct-⊒ (ƛ t) {ρ} {c} {s} {k} n hyp =
    let m , h = hyp (T.ƛ t ρ) in
      1 + m
    , (run (⟦ ƛ t ⟧′ ρ n >>= k)                                            ⊑⟨⟩
       run (k (T.ƛ t ρ))                                                   ⊑⟨ h ⟩
       steps ⟨ c , val (comp-val (T.ƛ t ρ)) ∷ s , comp-env ρ ⟩ (m + n)     ⊑⟨⟩
       steps ⟨ clo (comp t (ret ∷ [])) ∷ c , s , comp-env ρ ⟩ (1 + m + n)  ■)

  ⟦⟧-correct-⊒ (t₁ · t₂) {ρ} {c} {s} {k} n hyp =
    let m , h = ⟦⟧-correct-⊒ t₁ n λ v₁ →
                ⟦⟧-correct-⊒ t₂ n λ v₂ →
                ∙-correct-⊒ v₁ v₂ n hyp in
      m
    , (run (⟦ t₁ · t₂ ⟧′ ρ n >>= k)                                    ⊑⟨ (cong MaybeT.run $ sym $ Monad.associativity tr (⟦ t₁ ⟧′ ρ n) _ _) ⟩≡

       run (⟦ t₁ ⟧′ ρ n >>= λ v₁ →
            (⟦ t₂ ⟧′ ρ n >>= λ v₂ → (v₁ ∙ v₂) n) >>= k)                ⊑⟨ (cong (λ f → run (⟦ t₁ ⟧′ ρ n >>= f))
                                                                                (ext λ v₁ → sym $ Monad.associativity tr (⟦ t₂ ⟧′ ρ n) _ _)) ⟩≡
       run (⟦ t₁ ⟧′ ρ n >>= λ v₁ →
            ⟦ t₂ ⟧′ ρ n >>= λ v₂ →
            (v₁ ∙ v₂) n >>= k)                                         ⊑⟨ h ⟩

       steps ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩ (m + n)  ■)
    where
    tr = Monad-transformer.transform (Maybe.monad-transformer ext)

  ∙-correct-⊒ :
    ∀ {n} v₁ v₂ {ρ : T.Env n} {c s} {k : T.Value → M C.Value} n →
    (∀ v → ∃ λ m →
       steps ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ (m + n) ⊒
       run (k v)) →
    ∃ λ m →
      steps ⟨ app ∷ c
            , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s
            , comp-env ρ
            ⟩ (m + n) ⊒
      run ((v₁ ∙ v₂) n >>= k)

  ∙-correct-⊒ (T.con i) v₂ {ρ} {c} {s} {k} n hyp =
      0
    , (run ((T.con i ∙ v₂) n >>= k)                   ⊑⟨⟩
       run fail                                       ⊑⟨⟩
       steps ⟨ app ∷ c
             , val (comp-val v₂) ∷ val (C.con i) ∷ s
             , comp-env ρ
             ⟩ n                                      ■)

  ∙-correct-⊒ (T.ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} zero hyp =
      0
    , (run ((T.ƛ t₁ ρ₁ ∙ v₂) 0 >>= k)                              ⊑⟨⟩
       never                                                       ⊑⟨⟩
       steps ⟨ app ∷ c
             , val (comp-val v₂) ∷ val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
             , comp-env ρ
             ⟩ 0                                                   ■)

  ∙-correct-⊒ (T.ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} (suc n) hyp =
    let m , h = ⟦⟧-correct-⊒ t₁ n λ v →

          let m , h = hyp v in
            2 + m
          , (run (k v)                                                    ⊑⟨ h ⟩

             steps ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ (m + suc n)  ⊑⟨ cong (steps ⟨ c , _ , _ ⟩) (sym $ suc+≡+suc m) ⟩≡

             steps ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ (1 + m + n)  ⊑⟨⟩

             steps ⟨ ret ∷ []
                   , val (comp-val v) ∷ ret c (comp-env ρ) ∷ s
                   , comp-env (snoc ρ₁ v₂)
                   ⟩ (2 + m + n)                                          ■)
    in
      m
    , (run ((T.ƛ t₁ ρ₁ ∙ v₂) (suc n) >>= k)                       ⊑⟨⟩

       run (⟦ t₁ ⟧′ (snoc ρ₁ v₂) n >>= k)                         ⊑⟨ h ⟩

       steps ⟨ comp t₁ (ret ∷ [])
             , ret c (comp-env ρ) ∷ s
             , comp-env (snoc ρ₁ v₂)
             ⟩ (m + n)                                            ⊑⟨ cong (λ ρ′ → steps ⟨ comp t₁ (ret ∷ []) , ret c (comp-env ρ) ∷ s , ρ′ ⟩
                                                                                        (m + n))
                                                                          (ext (maybe (λ _ → refl) refl)) ⟩≡
       steps ⟨ comp t₁ (ret ∷ [])
             , ret c (comp-env ρ) ∷ s
             , snoc (comp-env ρ₁) (comp-val v₂)
             ⟩ (m + n)                                            ⊑⟨⟩

       steps ⟨ app ∷ c
             , val (comp-val v₂) ∷
               val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
             , comp-env ρ
             ⟩ (1 + m + n)                                        ⊑⟨ cong (steps ⟨ app ∷ _ , val _ ∷ val (comp-val (T.ƛ t₁ ρ₁)) ∷ _ , _ ⟩)
                                                                          (suc+≡+suc m) ⟩≡
       steps ⟨ app ∷ c
             , val (comp-val v₂) ∷
               val (comp-val (T.ƛ t₁ ρ₁)) ∷ s
             , comp-env ρ
             ⟩ (m + suc n)                                        ■)

-- Note that the equality that is used here is syntactic.

correct :
  ∀ t →
  wrap (exec ⟨ comp t [] , [] , empty ⟩) ≡
  (⟦ t ⟧ empty >>= λ v → return (comp-val v))
correct t =
  wrap (exec ⟨ comp t [] , [] , empty ⟩)                  ≡⟨ cong (λ ρ → wrap (exec ⟨ comp t [] , [] , ρ ⟩)) (ext λ ()) ⟩

  wrap (exec ⟨ comp t [] , [] , comp-env empty ⟩)         ≡⟨⟩

  wrap (⨆ (stepsˢ ⟨ comp t [] , [] , comp-env empty ⟩))   ≡⟨ cong wrap $ antisymmetry
                                                               (⨆-mono λ n → ⟦⟧-correct-⊑ t n λ v → MaybeT.run (return (comp-val v)) ■)
                                                               (least-upper-bound _ _ λ n →
                                                                  let m , h = ⟦⟧-correct-⊒ t n λ v →
                                                                                 0 , (MaybeT.run (return (comp-val v)) ■) in
      run (⟦ t ⟧′ empty n >>= λ v → return (comp-val v))          ⊑⟨ h ⟩
      steps ⟨ comp t [] , [] , comp-env empty ⟩ (m + n)           ⊑⟨ upper-bound _ _ ⟩■
      ⨆ (stepsˢ ⟨ comp t [] , [] , comp-env empty ⟩)              ■) ⟩

  wrap (⨆ (⟦ t ⟧ˢ empty >>=ˢ λ v →
           constˢ (MaybeT.run (return (comp-val v)))))    ≡⟨ cong (λ s → wrap (⨆ s))
                                                                  (_↔_.to equality-characterisation-increasing (λ _ → refl)) ⟩∎
  (⟦ t ⟧ empty >>= λ v → return (comp-val v))             ∎
