------------------------------------------------------------------------
-- Various properties
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Delay-monad.Alternative.Properties where

open import Equality.Propositional.Cubical
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (↑)

open import Bijection equality-with-J as Bijection using (_↔_)
open import Embedding equality-with-J as Embedding using (Embedding)
open import Equality.Decision-procedures equality-with-J
import Equality.Groupoid equality-with-J as EG
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J hiding (id; _∘_)
open import Groupoid equality-with-J
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import Injection equality-with-J using (Injective)
import Nat equality-with-J as N

open import Delay-monad.Alternative

------------------------------------------------------------------------
-- Lemmas related to h-levels

module _ {a} {A : Type a} where

  -- _↑ is a family of propositions.

  ↑-propositional : (x : Maybe A) → Is-proposition (x ↑)
  ↑-propositional nothing =
                                        $⟨ mono (N.zero≤ 2) ⊤-contractible ⟩
    Is-proposition (tt ≡ tt)            ↝⟨ H-level.respects-surjection (_↔_.surjection Bijection.≡↔inj₁≡inj₁) 1 ⟩□
    Is-proposition (nothing ≡ nothing)  □

  ↑-propositional (just x) = [inhabited⇒+]⇒+ 0 (

    just x ≡ nothing           ↝⟨ ⊎.inj₁≢inj₂ ∘ sym ⟩
    ⊥₀                         ↝⟨ ⊥-elim ⟩□
    Is-proposition (just x ↑)  □)

  -- LE nothing is a family of contractible types.

  LE-nothing-contractible :
    {x : Maybe A} → Contractible (LE nothing x)
  LE-nothing-contractible {x = x} =
    propositional⇒inhabited⇒contractible
      (λ where
         (inj₁ x↑)        (inj₂ (_ , ¬x↑)) → ⊥-elim (¬x↑ (sym x↑))
         (inj₂ (_ , ¬x↑)) (inj₁ x↑)        → ⊥-elim (¬x↑ (sym x↑))

         (inj₁ p)         (inj₁ q)         →
                                 $⟨ ↑-propositional _ ⟩
           Is-proposition (x ↑)  ↝⟨ (λ hyp → hyp _ _) ⦂ (_ → _) ⟩
           sym p ≡ sym q         ↔⟨ Eq.≃-≡ $ from-bijection $ Groupoid.⁻¹-bijection (EG.groupoid _) ⟩
           p ≡ q                 ↔⟨ Bijection.≡↔inj₁≡inj₁ ⟩□
           inj₁ p ≡ inj₁ q       □

         (inj₂ p) (inj₂ q) →
                                               $⟨ ×-closure 1 (↑-propositional _) (¬-propositional ext) ⟩
           Is-proposition (nothing ↑ × ¬ x ↑)  ↝⟨ (λ hyp → hyp _ _) ⦂ (_ → _) ⟩
           p ≡ q                               ↔⟨ Bijection.≡↔inj₂≡inj₂ ⟩□
           inj₂ p ≡ inj₂ q                     □)
      (case x return LE nothing of λ where
         nothing  → inj₁ refl
         (just x) → inj₂ (refl , ⊎.inj₁≢inj₂ ∘ sym))

  -- If A is a set, then LE is a family of propositions.

  LE-propositional :
    Is-set A → {x y : Maybe A} → Is-proposition (LE x y)
  LE-propositional A-set = irr _ _
    where
    irr : ∀ x y → Is-proposition (LE x y)
    irr nothing _ = mono₁ 0 LE-nothing-contractible

    irr (just x) (just y) (inj₁ p) (inj₁ q) =
      cong inj₁ $ Maybe-closure 0 A-set p q

    irr (just _) (just _) (inj₂ (() , _))
    irr (just _) (just _) _ (inj₂ (() , _))
    irr (just _) nothing  (inj₁ ())
    irr (just _) nothing  (inj₂ (() , _))

  -- If A is a set, then Increasing is a family of propositions.

  Increasing-propositional :
    Is-set A → {f : ℕ → Maybe A} → Is-proposition (Increasing f)
  Increasing-propositional A-set =
    Π-closure ext 1 λ _ →
    LE-propositional A-set

  -- An equality characterisation lemma which applies when A is a set.

  equality-characterisation :
    Is-set A →
    {x y : Delay A} → proj₁ x ≡ proj₁ y ↔ x ≡ y
  equality-characterisation A-set =
    ignore-propositional-component (Increasing-propositional A-set)

  -- If A has h-level 2 + n, then LE {A = A} x y has h-level 2 + n.

  LE-closure :
    ∀ {x y} n → H-level (2 + n) A → H-level (2 + n) (LE x y)
  LE-closure n h =
    ⊎-closure n
      (mono₁ (1 + n) (Maybe-closure n h))
      (mono (N.suc≤suc (N.zero≤ (1 + n)))
         (×-closure 1 (↑-propositional _)
                      (¬-propositional ext)))

  -- If A has h-level 2 + n, then Increasing {A = A} f has h-level
  -- 2 + n.

  Increasing-closure :
    ∀ {f} n → H-level (2 + n) A → H-level (2 + n) (Increasing f)
  Increasing-closure n h =
    Π-closure ext (2 + n) λ _ →
    LE-closure n h

  -- If A has h-level 2 + n, then Delay A has h-level 2 + n.

  Delay-closure :
    ∀ n → H-level (2 + n) A → H-level (2 + n) (Delay A)
  Delay-closure n h =
    Σ-closure (2 + n)
      (Π-closure ext (2 + n) λ _ →
       Maybe-closure n h)
      (λ _ → Increasing-closure n h)

------------------------------------------------------------------------
-- Various properties relating _↓_, _↑ and the usual ordering of the
-- natural numbers

module _ {a} {A : Type a} where

  -- If f is increasing and f n has a value, then f (suc n) has the
  -- same value.

  ↓-step : ∀ {f} {x : A} {n} →
           Increasing f → f n ↓ x → f (suc n) ↓ x
  ↓-step {f = f} {x} {n} inc fn↓x = step (inc n)
    module ↓ where
    step : LE (f n) (f (suc n)) → f (suc n) ↓ x
    step (inj₁ fn≡f1+n) =

      f (suc n)  ≡⟨ sym fn≡f1+n ⟩
      f n        ≡⟨ fn↓x ⟩∎
      just x     ∎

    step (inj₂ (fn↑ , _)) =

      ⊥-elim $ ⊎.inj₁≢inj₂ (
        nothing  ≡⟨ sym fn↑ ⟩
        f n      ≡⟨ fn↓x ⟩∎
        just x   ∎)

  -- If f is increasing and f (suc n) does not have a value, then
  -- f n does not have a value.

  ↑-step : ∀ {f : ℕ → Maybe A} {n} →
           Increasing f → f (suc n) ↑ → f n ↑
  ↑-step {f} {n} inc f1+n↑ with inc n
  ... | inj₁ fn≡f1+n   = f n        ≡⟨ fn≡f1+n ⟩
                         f (suc n)  ≡⟨ f1+n↑ ⟩∎
                         nothing    ∎
  ... | inj₂ (fn↑ , _) = fn↑

  -- If f is increasing and f 0 has a value, then f n has the same
  -- value.

  ↓-upwards-closed₀ : ∀ {f} {x : A} →
                      Increasing f → f 0 ↓ x → ∀ n → f n ↓ x
  ↓-upwards-closed₀ _   f0↓ zero    = f0↓
  ↓-upwards-closed₀ inc f0↓ (suc n) =
    ↓-upwards-closed₀ (inc ∘ suc) (↓-step inc f0↓) n

  -- If f is increasing, then (λ n → f n ↓ x) is upwards closed.

  ↓-upwards-closed :
    ∀ {f : ℕ → Maybe A} {m n x} →
    Increasing f → m N.≤ n → f m ↓ x → f n ↓ x
  ↓-upwards-closed _   (N.≤-refl′ refl)     = id
  ↓-upwards-closed inc (N.≤-step′ m≤n refl) =
    ↓-step inc ∘ ↓-upwards-closed inc m≤n

  -- If f is increasing, then (λ n → f n ↑) is downwards closed.

  ↑-downwards-closed : ∀ {f : ℕ → Maybe A} {m n} →
                       Increasing f → m N.≤ n → f n ↑ → f m ↑
  ↑-downwards-closed inc (N.≤-refl′ refl)     = id
  ↑-downwards-closed inc (N.≤-step′ m≤n refl) =
    ↑-downwards-closed inc m≤n ∘ ↑-step inc

  -- If f is increasing and f m does not have a value, but f n does
  -- have a value, then m < n.

  ↑<↓ : ∀ {f : ℕ → Maybe A} {x m n} →
        Increasing f → f m ↑ → f n ↓ x → m N.< n
  ↑<↓ {f} {x} {m} {n} inc fm↑ fn↓x with n N.≤⊎> m
  ... | inj₂ m<n = m<n
  ... | inj₁ n≤m =
    ⊥-elim $ ⊎.inj₁≢inj₂
      (nothing  ≡⟨ sym $ ↑-downwards-closed inc n≤m fm↑ ⟩
       f n      ≡⟨ fn↓x ⟩∎
       just x   ∎)

------------------------------------------------------------------------
-- An unused lemma

private

  -- If the embedding g maps nothing to nothing and just to just, then
  -- there is an isomorphism between Increasing f and
  -- Increasing (g ∘ f).

  Increasing-∘ :
    ∀ {a b} {A : Type a} {B : Type b} {f : ℕ → Maybe A} →
    (g : Embedding (Maybe A) (Maybe B)) →
    Embedding.to g nothing ≡ nothing →
    (∀ {x} → Embedding.to g (just x) ≢ nothing) →
    Increasing f ↔ Increasing (Embedding.to g ∘ f)
  Increasing-∘ {A = A} {B} {f} g g↑ g↓ = record
    { surjection = record
      { logical-equivalence = record
        { to   = to   ∘_
        ; from = from ∘_
        }
      ; right-inverse-of = ⟨ext⟩ ∘ (to∘from ∘_)
      }
    ; left-inverse-of = ⟨ext⟩ ∘ (from∘to ∘_)
    }
    where
    g′ : Maybe A → Maybe B
    g′ = Embedding.to g

    g-injective : Injective g′
    g-injective = Embedding.injective (Embedding.is-embedding g)

    lemma₁ : ∀ {x} → x ↑ → g′ x ↑
    lemma₁ refl = g↑

    lemma₂ : ∀ x → ¬ x ↑ → ¬ g′ x ↑
    lemma₂ nothing  x↓ _ = x↓ refl
    lemma₂ (just _) _    = g↓

    lemma₃ : ∀ x → g′ x ↑ → x ↑
    lemma₃ nothing  _   = refl
    lemma₃ (just _) g↓↑ = ⊥-elim (lemma₂ _ (λ ()) g↓↑)

    lemma₄ : ∀ x → g′ x ≢ nothing → x ≢ nothing
    lemma₄ nothing  g↑↓ _  = g↑↓ g↑
    lemma₄ (just _) _   ()

    to : ∀ {n} → Increasing-at n f → Increasing-at n (g′ ∘ f)
    to = ⊎-map (cong g′) (Σ-map lemma₁ (lemma₂ _))

    from : ∀ {n} → Increasing-at n (g′ ∘ f) → Increasing-at n f
    from = ⊎-map g-injective (Σ-map (lemma₃ _) (lemma₄ _))

    to∘from : ∀ {n} (x : Increasing-at n (g′ ∘ f)) → to (from x) ≡ x
    to∘from (inj₁ p) = cong inj₁ (
      cong g′ (g-injective p)  ≡⟨ _≃_.right-inverse-of (Embedding.equivalence g) _ ⟩∎
      p                        ∎)
    to∘from (inj₂ _) = cong inj₂ $
      ×-closure 1 (↑-propositional _) (¬-propositional ext) _ _

    from∘to : ∀ {n} (x : Increasing-at n f) → from (to x) ≡ x
    from∘to (inj₁ p) = cong inj₁ (
      g-injective (cong g′ p)  ≡⟨ _≃_.left-inverse-of (Embedding.equivalence g) _ ⟩∎
      p                        ∎)
    from∘to (inj₂ _) = cong inj₂ $
      ×-closure 1 (↑-propositional _) (¬-propositional ext) _ _
