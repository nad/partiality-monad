------------------------------------------------------------------------
-- Fixpoint combinators
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Partiality-monad.Inductive.Fixpoints where

open import Equality.Propositional
open import Interval using (ext)
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Monad equality-with-J

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Monad
open import Partiality-monad.Inductive.Monotone
open import Partiality-monad.Inductive.Omega-continuous
open import Partiality-monad.Inductive.Properties

------------------------------------------------------------------------
-- A fixpoint combinator

module _ {a} {A : Set a} where

  -- Repeated composition of a monotone function with itself.

  comp : [ A ⊥→ A ⊥]⊑ → ℕ → [ A ⊥→ A ⊥]⊑
  comp f zero    = id⊑
  comp f (suc n) = comp f n ∘⊑ f

  -- Pre-composition with the function is pointwise equal to
  -- post-composition with the function.

  pre≡post : ∀ f n {x} →
             proj₁ (comp f n ∘⊑ f) x ≡ proj₁ (f ∘⊑ comp f n) x
  pre≡post f zero        = refl
  pre≡post f (suc n) {x} =
    proj₁ (comp f n ∘⊑ f) (proj₁ f x)  ≡⟨ pre≡post f n ⟩∎
    proj₁ (f ∘⊑ comp f n) (proj₁ f x)  ∎

  -- An increasing sequence consisting of repeated applications of the
  -- given monotone function to never.

  fix-sequence : [ A ⊥→ A ⊥]⊑ → Increasing-sequence A
  fix-sequence f =
      (λ n → proj₁ (comp f n) never)
    , (λ n →
         proj₁ (comp f n) never            ⊑⟨ proj₂ (comp f n) (never⊑ (proj₁ f never)) ⟩■
         proj₁ (comp f n) (proj₁ f never)  ■)

  -- Taking the tail of this sequence amounts to the same thing as
  -- applying the function to each element in the sequence.

  tailˢ-fix-sequence :
    (f : [ A ⊥→ A ⊥]⊑) →
    tailˢ (fix-sequence f) ≡ [ f $ fix-sequence f ]-inc
  tailˢ-fix-sequence f =
    _↔_.to equality-characterisation-increasing λ n →
      proj₁ (comp f n ∘⊑ f) never  ≡⟨ pre≡post f n ⟩∎
      proj₁ (f ∘⊑ comp f n) never  ∎

  -- The sequence has the same least upper bound as the sequence you
  -- get if you apply the function to each element of the sequence.

  ⨆-fix-sequence :
    (f : [ A ⊥→ A ⊥]⊑) →
    ⨆ (fix-sequence f) ≡ ⨆ [ f $ fix-sequence f ]-inc
  ⨆-fix-sequence f =
    ⨆ (fix-sequence f)            ≡⟨ sym $ ⨆tail≡⨆ _ ⟩
    ⨆ (tailˢ (fix-sequence f))    ≡⟨ cong ⨆ (tailˢ-fix-sequence f) ⟩∎
    ⨆ [ f $ fix-sequence f ]-inc  ∎

  -- A fixpoint combinator.

  fix : [ A ⊥→ A ⊥]⊑ → A ⊥
  fix f = ⨆ (fix-sequence f)

  -- The fixpoint combinator produces fixpoints for ω-continuous
  -- arguments.

  fix-is-fixpoint-combinator :
    (fω : [ A ⊥→ A ⊥]) →
    let f⊑ : [ A ⊥→ A ⊥]⊑
        f⊑ = proj₁ fω

        f : A ⊥ → A ⊥
        f = proj₁ f⊑
    in fix f⊑ ≡ f (fix f⊑)
  fix-is-fixpoint-combinator fω =
    fix f⊑                          ≡⟨⟩
    ⨆ (fix-sequence f⊑)             ≡⟨ ⨆-fix-sequence f⊑ ⟩
    ⨆ [ f⊑ $ fix-sequence f⊑ ]-inc  ≡⟨ sym $ proj₂ fω _ ⟩
    f (⨆ (fix-sequence f⊑))         ≡⟨ refl ⟩∎
    f (fix f⊑)                      ∎
    where
    f⊑ : [ A ⊥→ A ⊥]⊑
    f⊑ = proj₁ fω

    f : A ⊥ → A ⊥
    f = proj₁ f⊑

  -- A variant of fix.

  fix′ : (A → A ⊥) → A ⊥
  fix′ f = fix (proj₁ (f ∗))

  -- This variant also produces a kind of fixpoint.

  fix′-is-fixpoint-combinator :
    (f : A → A ⊥) →
    fix′ f ≡ fix′ f >>= f
  fix′-is-fixpoint-combinator f =
    fix′ f                   ≡⟨⟩
    fix (proj₁ (f ∗))        ≡⟨ fix-is-fixpoint-combinator (f ∗) ⟩∎
    fix (proj₁ (f ∗)) >>= f  ∎

------------------------------------------------------------------------
-- Another fixpoint combinator

-- TODO: Is it possible to find some suitable abstraction and have
-- only one implementation of a fixpoint combinator?

-- Partial function transformers.

Trans : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Trans A B = (A → B ⊥) → (A → B ⊥)

-- Monotone partial function transformers.

Trans-⊑ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Trans-⊑ A B = ∃ λ (f : (A → B ⊥) → (A → B ⊥)) →
            ∀ {g₁ g₂} → (∀ x → g₁ x ⊑ g₂ x) → ∀ x → f g₁ x ⊑ f g₂ x

-- Monotone partial function transformers can be turned into
-- parametrised increasing sequence transformers.

[_$_at_]-inc :
  ∀ {a b} {A : Set a} {B : Set b} →
  Trans-⊑ A B →
  (A → Increasing-sequence B) → (A → Increasing-sequence B)
[ f $ s at x ]-inc =
    (λ n → proj₁ f (λ x → s x [ n ]) x)
  , (λ n → proj₂ f (λ x → increasing (s x) n) x)

-- Partial function transformers that are ω-continuous.

Trans-ω : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Trans-ω A B = ∃ λ (f : Trans-⊑ A B) →
                (s : A → Increasing-sequence B) (x : A) →
                proj₁ f (⨆ ∘ s) x ≡ ⨆ [ f $ s at x ]-inc

module _ {a b} {A : Set a} {B : Set b} where

  -- Repeated application of a partial function transformer to never.

  app : Trans A B → ℕ → (A → B ⊥)
  app f zero    = const never
  app f (suc n) = f (app f n)

  -- An increasing sequence consisting of repeated applications of the
  -- given partial function transformer to never.

  fix→-sequence : (f : Trans-⊑ A B) → A → Increasing-sequence B
  fix→-sequence f x =
      (λ n → app (proj₁ f) n x)
    , (λ n →
         app (proj₁ f) n       x  ⊑⟨ app-increasing n x ⟩■
         app (proj₁ f) (suc n) x  ■)
    where
    app-increasing :
      ∀ n x → app (proj₁ f) n x ⊑ app (proj₁ f) (suc n) x
    app-increasing zero    = never⊑ ∘ proj₁ f (const never)
    app-increasing (suc n) = proj₂ f (app-increasing n)

  -- A fixpoint combinator.

  fix→ : Trans-⊑ A B → (A → B ⊥)
  fix→ f x = ⨆ (fix→-sequence f x)

  -- The fixpoint combinator produces fixpoints for ω-continuous
  -- arguments.

  fix→-is-fixpoint-combinator :
    (fω : Trans-ω A B) →
    let f⊑ : Trans-⊑ A B
        f⊑ = proj₁ fω

        f : Trans A B
        f = proj₁ f⊑
    in
    fix→ f⊑ ≡ f (fix→ f⊑)
  fix→-is-fixpoint-combinator (f , ω-cont) = ext λ x →
    fix→ f x                            ≡⟨⟩
    ⨆ (fix→-sequence f x)               ≡⟨ sym $ ⨆tail≡⨆ _ ⟩
    ⨆ (tailˢ (fix→-sequence f x))       ≡⟨ cong ⨆ (_↔_.to equality-characterisation-increasing (λ _ → refl)) ⟩
    ⨆ [ f $ fix→-sequence f at x ]-inc  ≡⟨ sym $ ω-cont (fix→-sequence f) x ⟩
    proj₁ f (⨆ ∘ fix→-sequence f) x     ≡⟨ refl ⟩∎
    proj₁ f (fix→ f) x                  ∎
