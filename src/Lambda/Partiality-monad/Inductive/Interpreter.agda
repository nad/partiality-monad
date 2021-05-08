------------------------------------------------------------------------
-- A definitional interpreter
------------------------------------------------------------------------

{-# OPTIONS --cubical --sized-types #-}

module Lambda.Partiality-monad.Inductive.Interpreter where

open import Equality.Propositional.Cubical
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J hiding (id; _∘_)
open import Maybe equality-with-J
open import Monad equality-with-J
open import Vec.Function equality-with-J

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Fixpoints
open import Partiality-monad.Inductive.Monad

open import Lambda.Syntax hiding ([_])

open Closure Tm

------------------------------------------------------------------------
-- An interpreter monad

-- The interpreter monad.

M : ∀ {ℓ} → Type ℓ → Type ℓ
M = MaybeT _⊥

-- Information ordering.

infix 4 _⊑M_

_⊑M_ : ∀ {a} {A : Type a} → M A → M A → Type a
x ⊑M y = run x ⊑ run y

-- Bind is monotone.

_>>=ᵐ-mono_ :
  ∀ {ℓ} {A B : Type ℓ} {x y : M A} {f g : A → M B} →
  x ⊑M y → (∀ z → f z ⊑M g z) → x >>= f ⊑M y >>= g
_>>=ᵐ-mono_ {x = x} {y} {f} {g} x⊑y f⊑g =
  run x >>= maybe (MaybeT.run ∘ f) (return nothing)  ⊑⟨ x⊑y >>=-mono maybe f⊑g (run fail ■) ⟩■
  run y >>= maybe (MaybeT.run ∘ g) (return nothing)  ■

-- A variant of bind for sequences.

infix 5 _>>=ˢ_

_>>=ˢ_ : {A B : Type} →
         Increasing-sequence (Maybe A) →
         (A → Increasing-sequence (Maybe B)) →
         Increasing-sequence (Maybe B)
s >>=ˢ f =
    (λ n → MaybeT.run (wrap (s [ n ]) >>= λ x → wrap (f x [ n ])))
  , (λ n → increasing s n >>=ᵐ-mono λ x → increasing (f x) n)

------------------------------------------------------------------------
-- One interpreter

module Interpreter₁ where

  -- This interpreter is defined as the least upper bound of a
  -- sequence of increasingly defined interpreters.

  infix 10 _∙_

  mutual

    ⟦_⟧′ : ∀ {n} → Tm n → Env n → ℕ → M Value
    ⟦ con i ⟧′   ρ n = return (con i)
    ⟦ var x ⟧′   ρ n = return (ρ x)
    ⟦ ƛ t ⟧′     ρ n = return (ƛ t ρ)
    ⟦ t₁ · t₂ ⟧′ ρ n = ⟦ t₁ ⟧′ ρ n >>= λ v₁ →
                       ⟦ t₂ ⟧′ ρ n >>= λ v₂ →
                       (v₁ ∙ v₂) n

    _∙_ : Value → Value → ℕ → M Value
    (con i  ∙ v₂) n       = fail
    (ƛ t₁ ρ ∙ v₂) zero    = liftʳ never
    (ƛ t₁ ρ ∙ v₂) (suc n) = ⟦ t₁ ⟧′ (cons v₂ ρ) n

  mutual

    ⟦⟧′-increasing :
      ∀ {n} (t : Tm n) ρ n → ⟦ t ⟧′ ρ n ⊑M ⟦ t ⟧′ ρ (suc n)
    ⟦⟧′-increasing (con i)   ρ n = MaybeT.run (return (con i)) ■
    ⟦⟧′-increasing (var x)   ρ n = MaybeT.run (return (ρ x))   ■
    ⟦⟧′-increasing (ƛ t)     ρ n = MaybeT.run (return (ƛ t ρ)) ■
    ⟦⟧′-increasing (t₁ · t₂) ρ n =
      ⟦⟧′-increasing t₁ ρ n >>=ᵐ-mono λ v₁ →
      ⟦⟧′-increasing t₂ ρ n >>=ᵐ-mono λ v₂ →
      ∙-increasing v₁ v₂ n

    ∙-increasing : ∀ v₁ v₂ n → (v₁ ∙ v₂) n ⊑M (v₁ ∙ v₂) (suc n)
    ∙-increasing (con i)  v₂ n       = run fail ■
    ∙-increasing (ƛ t₁ ρ) v₂ (suc n) = ⟦⟧′-increasing t₁ (cons v₂ ρ) n
    ∙-increasing (ƛ t₁ ρ) v₂ zero    =
      never >>= return ∘ just      ≡⟨ never->>= ⟩⊑
      never                        ⊑⟨ never⊑ _ ⟩■
      run (⟦ t₁ ⟧′ (cons v₂ ρ) 0)  ■

  ⟦_⟧ˢ : ∀ {n} → Tm n → Env n → Increasing-sequence (Maybe Value)
  ⟦ t ⟧ˢ ρ = MaybeT.run ∘ ⟦ t ⟧′ ρ , ⟦⟧′-increasing t ρ

  ⟦_⟧ : ∀ {n} → Tm n → Env n → M Value
  run (⟦ t ⟧ ρ) = ⨆ (⟦ t ⟧ˢ ρ)

------------------------------------------------------------------------
-- Another interpreter

module Interpreter₂ where

  -- This interpreter is defined using a fixpoint combinator.

  M′ : Type → Type₁
  M′ = MaybeT (Partial (∃ λ n → Tm n × Env n) (λ _ → Maybe Value))

  infix 10 _∙_

  _∙_ : Value → Value → M′ Value
  con i  ∙ v₂ = fail
  ƛ t₁ ρ ∙ v₂ = wrap (rec (_ , t₁ , cons v₂ ρ))

  ⟦_⟧′ : ∀ {n} → Tm n → Env n → M′ Value
  ⟦ con i ⟧′   ρ = return (con i)
  ⟦ var x ⟧′   ρ = return (ρ x)
  ⟦ ƛ t ⟧′     ρ = return (ƛ t ρ)
  ⟦ t₁ · t₂ ⟧′ ρ = ⟦ t₁ ⟧′ ρ >>= λ v₁ →
                   ⟦ t₂ ⟧′ ρ >>= λ v₂ →
                   v₁ ∙ v₂

  ⟦_⟧ : ∀ {n} → Tm n → Env n → M Value
  run (⟦ t ⟧ ρ) =
    fixP {A = ∃ λ n → Tm n × Env n}
         (λ { (_ , t , ρ) → run (⟦ t ⟧′ ρ) }) (_ , t , ρ)

------------------------------------------------------------------------
-- The two interpreters are pointwise equal

interpreters-equal :
  ∀ {n} (t : Tm n) ρ →
  Interpreter₁.⟦ t ⟧ ρ ≡ Interpreter₂.⟦ t ⟧ ρ
interpreters-equal = λ t ρ →
                                                           $⟨ ⟦⟧-lemma t ρ ⟩
  (∀ n → run (Interpreter₁.⟦ t ⟧′ ρ n) ≡
         app→ step₂ (suc n) (_ , t , ρ))                   ↝⟨ cong ⨆ ∘ _↔_.to equality-characterisation-increasing ⟩

  ⨆ (Interpreter₁.⟦ t ⟧ˢ ρ) ≡
  ⨆ (tailˢ (at (fix→-sequence step₂) (_ , t , ρ)))         ↝⟨ flip trans (⨆tail≡⨆ _) ⟩

  ⨆ (Interpreter₁.⟦ t ⟧ˢ ρ) ≡
  ⨆ (at (fix→-sequence step₂) (_ , t , ρ))                 ↝⟨ id ⟩

  run (Interpreter₁.⟦ t ⟧ ρ) ≡ run (Interpreter₂.⟦ t ⟧ ρ)  ↝⟨ cong wrap ⟩□

  Interpreter₁.⟦ t ⟧ ρ ≡ Interpreter₂.⟦ t ⟧ ρ              □
  where
  open Partial
  open Trans-⊑

  step₂ : Trans-⊑ (∃ λ n → Tm n × Env n) (λ _ → Maybe Value)
  step₂ = transformer λ { (_ , t , ρ) → run (Interpreter₂.⟦ t ⟧′ ρ) }

  mutual

    ⟦⟧-lemma :
      ∀ {n} (t : Tm n) ρ n →
      run (Interpreter₁.⟦ t ⟧′ ρ n) ≡
      function (run (Interpreter₂.⟦ t ⟧′ ρ)) (app→ step₂ n)
    ⟦⟧-lemma (con i)   ρ n = refl
    ⟦⟧-lemma (var x)   ρ n = refl
    ⟦⟧-lemma (ƛ t)     ρ n = refl
    ⟦⟧-lemma (t₁ · t₂) ρ n =
      cong₂ _>>=_ (⟦⟧-lemma t₁ ρ n) $ ⟨ext⟩ $ flip maybe refl λ v₁ →
      cong₂ _>>=_ (⟦⟧-lemma t₂ ρ n) $ ⟨ext⟩ $ flip maybe refl λ v₂ →
      ∙-lemma v₁ v₂ n

    ∙-lemma :
      ∀ v₁ v₂ n →
      run ((v₁ Interpreter₁.∙ v₂) n) ≡
      function (run (v₁ Interpreter₂.∙ v₂)) (app→ step₂ n)
    ∙-lemma (con i)  v₂ n       = refl
    ∙-lemma (ƛ t₁ ρ) v₂ zero    = never >>= return ∘ just  ≡⟨ never->>= ⟩∎
                                  never                    ∎
    ∙-lemma (ƛ t₁ ρ) v₂ (suc n) = ⟦⟧-lemma t₁ (cons v₂ ρ) n

-- Let us use Interpreter₁ as the default interpreter.

open Interpreter₁ public

------------------------------------------------------------------------
-- An example

-- The semantics of Ω is the non-terminating computation never.

Ω-loops : run (⟦ Ω ⟧ nil) ≡ never
Ω-loops =
  antisymmetry (least-upper-bound _ _ lemma) (never⊑ _)
  where
  ω-nil = ƛ (var fzero · var fzero) nil

  reduce-twice :
    ∀ n → run (⟦ Ω ⟧′ nil n) ≡ run ((ω-nil ∙ ω-nil) n)
  reduce-twice n =
    run (⟦ Ω ⟧′ nil n)                            ≡⟨ now->>= ⟩
    run (⟦ ω ⟧′ nil n >>= λ v₂ → (ω-nil ∙ v₂) n)  ≡⟨ now->>= ⟩∎
    run ((ω-nil ∙ ω-nil) n)                       ∎

  lemma : ∀ n → run (⟦ Ω ⟧′ nil n) ⊑ never
  lemma zero    =
    run (⟦ Ω ⟧′ nil zero)       ≡⟨ reduce-twice zero ⟩⊑
    run ((ω-nil ∙ ω-nil) zero)  ≡⟨ never->>= ⟩⊑
    never                       ■
  lemma (suc n) =
    run (⟦ Ω ⟧′ nil (suc n))  ≡⟨ reduce-twice (suc n) ⟩⊑
    run (⟦ Ω ⟧′ nil n)        ⊑⟨ lemma n ⟩■
    never                     ■
