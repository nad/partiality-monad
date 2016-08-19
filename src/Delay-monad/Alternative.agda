------------------------------------------------------------------------
-- An alternative definition of the delay monad
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad.Alternative where

open import Equality.Propositional
open import H-level.Truncation.Propositional as Trunc
open import Interval
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (↑; module W)

open import Bijection equality-with-J as Bijection using (_↔_)
open import Equality.Decision-procedures equality-with-J
import Equality.Groupoid equality-with-J as EG
import Equivalence equality-with-J as Eq
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import Groupoid equality-with-J
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
import Nat equality-with-J as N

open import Delay-monad as D hiding (Delay)
import Delay-monad.Partial-order as PO
open import Delay-monad.Strong-bisimilarity as Strong-bisimilarity
import Delay-monad.Weak-bisimilarity as W

------------------------------------------------------------------------
-- _↓_ and _↑

module _ {a} {A : Set a} where

  infix 4 _↑ _↓_

  -- x ↓ y means that the computation x has the value y.

  _↓_ : Maybe A → A → Set a
  x ↓ y = x ≡ just y

  -- x ↑ means that the computation x does not have a value.

  _↑ : Maybe A → Set a
  x ↑ = x ≡ nothing

------------------------------------------------------------------------
-- An alternative definition of the delay monad

module _ {a} {A : Set a} where

  -- The property of being an increasing sequence.

  LE : Maybe A → Maybe A → Set a
  LE x y = x ≡ y ⊎ (x ↑ × ¬ y ↑)

  Increasing-at : ℕ → (ℕ → Maybe A) → Set a
  Increasing-at n f = LE (f n) (f (suc n))

  Increasing : (ℕ → Maybe A) → Set a
  Increasing f = ∀ n → Increasing-at n f

-- An alternative definition of the delay monad.

Delay : ∀ {a} → Set a → Set a
Delay A = ∃ λ (f : ℕ → Maybe A) → Increasing f

------------------------------------------------------------------------
-- Lemmas related to h-levels

module _ {a} {A : Set a} where

  -- _↑ is a family of propositions.

  ↑-propositional : (x : Maybe A) → Is-proposition (x ↑)
  ↑-propositional nothing =
                                        $⟨ mono (N.zero≤ 2) ⊤-contractible _ _ ⟩
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
      (_⇔_.from propositional⇔irrelevant λ
         { (inj₁ x↑)        (inj₂ (_ , ¬x↑)) → ⊥-elim (¬x↑ (sym x↑))
         ; (inj₂ (_ , ¬x↑)) (inj₁ x↑)        → ⊥-elim (¬x↑ (sym x↑))

         ; (inj₁ p)         (inj₁ q)         →
                                 $⟨ ↑-propositional _ ⟩
           Is-proposition (x ↑)  ↝⟨ (λ hyp → _⇔_.to propositional⇔irrelevant hyp _ _) ⟩
           sym p ≡ sym q         ↔⟨ Eq.≃-≡ $ from-bijection $ Groupoid.⁻¹-bijection (EG.groupoid _) ⟩
           p ≡ q                 ↔⟨ Bijection.≡↔inj₁≡inj₁ ⟩□
           inj₁ p ≡ inj₁ q       □

         ; (inj₂ p) (inj₂ q) →
                                               $⟨ ×-closure 1 (↑-propositional _) (¬-propositional ext) ⟩
           Is-proposition (nothing ↑ × ¬ x ↑)  ↝⟨ (λ hyp → _⇔_.to propositional⇔irrelevant hyp _ _) ⟩
           p ≡ q                               ↔⟨ Bijection.≡↔inj₂≡inj₂ ⟩□
           inj₂ p ≡ inj₂ q                     □
         })
      (case x return LE nothing of λ
         { nothing  → inj₁ refl
         ; (just x) → inj₂ (refl , ⊎.inj₁≢inj₂ ∘ sym)
         })

------------------------------------------------------------------------
-- Various properties relating _↓_, _↑ and the usual ordering of the
-- natural numbers

private

  module _ {a} {A : Set a} where

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

module _ {a} {A : Set a} where

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
  ↑<↓ {f} {x} {m} {n} inc fm↑ fn↓x with N.≤⊎> n m
  ... | inj₂ m<n = m<n
  ... | inj₁ n≤m =
    ⊥-elim $ ⊎.inj₁≢inj₂
      (nothing  ≡⟨ sym $ ↑-downwards-closed inc n≤m fm↑ ⟩
       f n      ≡⟨ fn↓x ⟩∎
       just x   ∎)

------------------------------------------------------------------------
-- Theorems relating the two definitions of the delay monad

-- The two definitions are logically equivalent.

private

  module LE {a} {A : Set a} where

    mutual

      to : Delay A → D.Delay A ∞
      to (f , increasing) = to′ (f 0)
        module To where
        to′ : Maybe A → D.Delay A ∞
        to′ (just x) = now x
        to′ nothing  =
          later (∞to (f ∘ suc , increasing ∘ suc))

      ∞to : Delay A → D.∞Delay A ∞
      force (∞to x) = to x

    from : D.Delay A ∞ → Delay A
    from = λ x → f x , f-increasing x
      where
      f : D.Delay A ∞ → ℕ → Maybe A
      f (now x)   _       = just x
      f (later x) zero    = nothing
      f (later x) (suc n) = f (force x) n

      f-increasing : ∀ x → Increasing (f x)
      f-increasing (now x)   _       = inj₁ refl
      f-increasing (later x) zero    = proj₁ LE-nothing-contractible
      f-increasing (later x) (suc n) = f-increasing (force x) n

module _ {a} {A : Set a} where

  Delay⇔Delay : Delay A ⇔ D.Delay A ∞
  Delay⇔Delay = record { to = LE.to; from = LE.from }

  -- The two definitions are isomorphic (assuming extensionality).

  Delay↔Delay : Strong-bisimilarity.Extensionality a →
                Delay A ↔ D.Delay A ∞
  Delay↔Delay delay-ext = record
    { surjection = record
      { logical-equivalence = Delay⇔Delay
      ; right-inverse-of    = delay-ext ∘ to∘from
      }
    ; left-inverse-of = from∘to
    }
    where
    open LE

    -- The function from is a right inverse of to.

    mutual

      to∘from : ∀ x → to (from x) ∼ x
      to∘from (now x)   = now-cong
      to∘from (later x) = later-cong (∞to∘from (force x))

      ∞to∘from : ∀ x → to (from x) ∞∼ x
      force (∞to∘from x) = to∘from x

    -- The proof showing that from is a left inverse of to is more
    -- complicated.

    from∘to : ∀ x → from (to x) ≡ x
    from∘to (g , g-inc) = Σ-≡,≡→≡
      (ext (proj₁∘from∘to g g-inc _ refl))
      (ext λ n →

         subst Increasing
               (ext (proj₁∘from∘to g g-inc _ refl))
               (proj₂ (from (to (g , g-inc))))
               n                                        ≡⟨ sym $ push-subst-application (ext (proj₁∘from∘to g g-inc _ refl)) Increasing-at ⟩

         subst (Increasing-at n)
               (ext (proj₁∘from∘to g g-inc _ refl))
               (proj₂ (from (to (g , g-inc))) n)        ≡⟨ proj₂∘from∘to g g-inc n _ refl ⟩∎

         g-inc n                                        ∎)

      where

      proj₁∘from∘to :
        (g : ℕ → Maybe A) →
        (g-increasing : Increasing g) →
        ∀ x → g 0 ≡ x → ∀ n →
        proj₁ (from (To.to′ g g-increasing x)) n ≡ g n
      proj₁∘from∘to g g-inc (just x) g0↓x n       = sym $ ↓-upwards-closed₀ g-inc g0↓x n
      proj₁∘from∘to g g-inc nothing  g0↑  zero    = sym g0↑
      proj₁∘from∘to g g-inc nothing  g0↑  (suc n) =
          proj₁∘from∘to (g ∘ suc) (g-inc ∘ suc) _ refl n

      ↓-lemma :
        (g : ℕ → Maybe A) →
        (g-increasing : Increasing g) →
        ∀ n x (g0↓x : g 0 ↓ x) p → p ≡ g-increasing 0 →

        subst (Increasing-at n)
              (ext (sym ∘ ↓-upwards-closed₀ g-increasing g0↓x))
              (inj₁ refl)
          ≡
        g-increasing n

      ↓-lemma g _ _ x g0↓x (inj₂ (g0↑ , _)) _ =
        ⊥-elim $ ⊎.inj₁≢inj₂ (
          nothing  ≡⟨ sym g0↑ ⟩
          g 0      ≡⟨ g0↓x ⟩∎
          just x   ∎)

      ↓-lemma g g-inc zero x g0↓x (inj₁ g0≡g1) ≡g-inc0 =

        subst (Increasing-at zero)
              (ext (sym ∘ ↓-upwards-closed₀ g-inc g0↓x))
              (inj₁ refl)                                       ≡⟨ push-subst-inj₁
                                                                     {y≡z = ext (sym ∘ ↓-upwards-closed₀ g-inc g0↓x)}
                                                                     (λ f → f 0 ≡ f 1) (λ f → f 0 ↑ × ¬ f 1 ↑) ⟩
        inj₁ (subst (λ f → f 0 ≡ f 1)
                    (ext (sym ∘ ↓-upwards-closed₀ g-inc g0↓x))
                    refl)                                       ≡⟨ cong inj₁ lemma ⟩

        inj₁ g0≡g1                                              ≡⟨ ≡g-inc0 ⟩∎

        g-inc zero                                              ∎

        where
        eq    = ↓-upwards-closed₀ g-inc g0↓x
        lemma =

          subst (λ f → f 0 ≡ f 1) (ext (sym ∘ eq)) refl      ≡⟨ subst-in-terms-of-trans-and-cong {x≡y = ext (sym ∘ eq)} ⟩

          trans (sym (cong (_$ 0) (ext (sym ∘ eq))))
                (trans refl (cong (_$ 1) (ext (sym ∘ eq))))  ≡⟨ cong (trans (sym (cong (_$ 0) (ext (sym ∘ eq))))) $
                                                                  trans-reflˡ (cong (_$ 1) (ext (sym ∘ eq))) ⟩
          trans (sym (cong (_$ 0) (ext (sym ∘ eq))))
                (cong (_$ 1) (ext (sym ∘ eq)))               ≡⟨ cong₂ (λ p q → trans (sym p) q) (cong-ext (sym ∘ eq)) (cong-ext (sym ∘ eq)) ⟩

          trans (sym $ sym $ eq 0) (sym $ eq 1)              ≡⟨ cong (λ eq′ → trans eq′ (sym $ eq 1)) $ sym-sym _ ⟩

          trans (eq 0) (sym $ eq 1)                          ≡⟨⟩

          trans g0↓x (sym $ ↓.step g-inc g0↓x (g-inc 0))     ≡⟨ cong (λ eq′ → trans g0↓x (sym $ ↓.step g-inc g0↓x eq′)) $ sym $ ≡g-inc0 ⟩

          trans g0↓x (sym $ ↓.step g-inc g0↓x (inj₁ g0≡g1))  ≡⟨⟩

          trans g0↓x (sym $ trans (sym g0≡g1) g0↓x)          ≡⟨ cong (trans g0↓x) $ sym-trans (sym g0≡g1) g0↓x ⟩

          trans g0↓x (trans (sym g0↓x) (sym (sym g0≡g1)))    ≡⟨ trans--[trans-sym] _ _ ⟩

          sym (sym g0≡g1)                                    ≡⟨ sym-sym _ ⟩∎

          g0≡g1                                              ∎

      ↓-lemma g g-inc (suc n) x g0↓x (inj₁ g0≡g1) ≡g-inc0 =

        subst (Increasing-at (suc n))
              (ext (sym ∘ ↓-upwards-closed₀ g-inc g0↓x))
              (inj₁ refl)                                               ≡⟨⟩

        subst (Increasing-at n ∘ (_∘ suc))
              (ext (sym ∘ ↓-upwards-closed₀ g-inc g0↓x))
              (inj₁ refl)                                               ≡⟨ subst-∘ (Increasing-at n) (_∘ suc)
                                                                                   (ext (sym ∘ ↓-upwards-closed₀ g-inc g0↓x)) ⟩
        subst (Increasing-at n)
              (cong (_∘ suc)
                 (ext (sym ∘ ↓-upwards-closed₀ g-inc g0↓x)))
              (inj₁ refl)                                               ≡⟨ cong (λ eq → subst (Increasing-at n) eq _) $
                                                                             cong-∘-ext (sym ∘ ↓-upwards-closed₀ g-inc g0↓x) ⟩
        subst (Increasing-at n)
              (ext (sym ∘ ↓-upwards-closed₀ g-inc g0↓x ∘ suc))
              (inj₁ refl)                                               ≡⟨⟩

        subst (Increasing-at n)
              (ext (sym ∘ ↓-upwards-closed₀ (g-inc ∘ suc)
                            (↓.step g-inc g0↓x (g-inc 0))))
              (inj₁ refl)                                               ≡⟨ cong (λ p → subst (Increasing-at n)
                                                                                             (ext (sym ∘ ↓-upwards-closed₀ (g-inc ∘ suc)
                                                                                                           (↓.step g-inc g0↓x p)))
                                                                                             (inj₁ refl))
                                                                                (sym ≡g-inc0) ⟩
        subst (Increasing-at n)
              (ext (sym ∘ ↓-upwards-closed₀ (g-inc ∘ suc)
                            (↓.step g-inc g0↓x (inj₁ g0≡g1))))
              (inj₁ refl)                                               ≡⟨⟩

        subst (Increasing-at n)
              (ext (sym ∘ ↓-upwards-closed₀ (g-inc ∘ suc)
                                            (trans (sym g0≡g1) g0↓x)))
              (inj₁ refl)                                               ≡⟨ ↓-lemma (g ∘ suc) (g-inc ∘ suc) n _ _ _ refl ⟩∎

        g-inc (suc n)                                                   ∎

      proj₂∘from∘to :
        (g : ℕ → Maybe A) →
        (g-increasing : Increasing g) →
        ∀ n y (g0≡y : g 0 ≡ y) →

        subst (Increasing-at n)
              (ext (proj₁∘from∘to g g-increasing y g0≡y))
              (proj₂ (from (To.to′ g g-increasing y)) n)
          ≡
        g-increasing n

      proj₂∘from∘to g g-inc n (just y) g0↓y =
        ↓-lemma g g-inc n y g0↓y _ refl

      proj₂∘from∘to g g-inc zero nothing g0↑ =
        _⇔_.to propositional⇔irrelevant
          (                                   $⟨ mono₁ 0 LE-nothing-contractible ⟩
           Is-proposition (LE nothing (g 1))  ↝⟨ subst (λ x → Is-proposition (LE x (g 1))) (sym g0↑) ⟩□
           Is-proposition (LE (g 0) (g 1))    □)
          _ _

      proj₂∘from∘to g g-inc (suc n) nothing g0↑ =

        subst (Increasing-at (suc n))
              (ext (proj₁∘from∘to g g-inc nothing g0↑))
              (proj₂ (from (to (g ∘ suc , g-inc ∘ suc))) n)              ≡⟨⟩

        subst (Increasing-at n ∘ (_∘ suc))
              (ext (proj₁∘from∘to g g-inc nothing g0↑))
              (proj₂ (from (to (g ∘ suc , g-inc ∘ suc))) n)              ≡⟨ subst-∘ (Increasing-at n) (_∘ suc)
                                                                                    (ext (proj₁∘from∘to g g-inc nothing g0↑)) ⟩
        subst (Increasing-at n)
              (cong (_∘ suc) (ext (proj₁∘from∘to g g-inc nothing g0↑)))
              (proj₂ (from (to (g ∘ suc , g-inc ∘ suc))) n)              ≡⟨ cong (λ eq → subst (Increasing-at n) eq _) $
                                                                              cong-∘-ext (proj₁∘from∘to g g-inc nothing g0↑) ⟩
        subst (Increasing-at n)
              (ext (proj₁∘from∘to g g-inc nothing g0↑ ∘ suc))
              (proj₂ (from (to (g ∘ suc , g-inc ∘ suc))) n)              ≡⟨⟩

        subst (Increasing-at n)
              (ext (proj₁∘from∘to (g ∘ suc) (g-inc ∘ suc) _ refl))
              (proj₂ (from (to (g ∘ suc , g-inc ∘ suc))) n)              ≡⟨ proj₂∘from∘to (g ∘ suc) (g-inc ∘ suc) n _ refl ⟩∎

        g-inc (suc n)                                                    ∎

------------------------------------------------------------------------
-- Termination predicates

module _ {a} {A : Set a} where

  infix 4 _⇓_ _∥⇓∥_ _⇓′_

  -- The three logically equivalent types x ⇓ y, x ∥⇓∥ y and x ⇓′ y
  -- all mean that the computation x terminates with the value y:
  --
  -- ∙ _⇓_ is the "obvious" definition. The definition does not
  --   involve truncation, and can be used directly.
  --
  -- ∙ _∥⇓∥_ is a truncated variant of _⇓_. It may be more convenient
  --   to construct values of type x ∥⇓∥ y than of type x ⇓ y, because
  --   the former type is a proposition.
  --
  -- ∙ _⇓′_ is an auxiliary definition, used to prove that the other
  --   two are logically equivalent. This definition does not use
  --   truncation, but is still propositional (if A is a set).

  _⇓_ : Delay A → A → Set a
  (f , _) ⇓ y = ∃ λ n → f n ↓ y

  _∥⇓∥_ : Delay A → A → Set a
  x ∥⇓∥ y = ∥ x ⇓ y ∥

  _⇓′_ : Delay A → A → Set _
  (f , _) ⇓′ y = ∃ λ m → f m ↓ y × (∀ n → ¬ f n ↑ → m N.≤ n)

  -- _⇓′_ is a family of propositions (if A is a set).

  ⇓′-propositional :
    Is-set A → ∀ x {y : A} → Is-proposition (x ⇓′ y)
  ⇓′-propositional A-set x@(f , _) {y} =
    _⇔_.from propositional⇔irrelevant λ p q →

                         $⟨ number-unique p q ⟩
      proj₁ p ≡ proj₁ q  ↝⟨ ignore-propositional-component
                              (×-closure 1 (Maybe-closure 0 A-set _ _)
                                           (Π-closure ext 1 λ _ →
                                            Π-closure ext 1 λ _ →
                                            ≤-propositional)) ⟩□
      p ≡ q              □

    where
    number-unique : (p q : x ⇓′ y) → proj₁ p ≡ proj₁ q
    number-unique (pm , f-pm↓y , pm≤) (qm , f-qm↓y , qm≤) =
      N.≤-antisymmetric
        (pm≤ qm λ f-qm↑ → ⊎.inj₁≢inj₂ (nothing  ≡⟨ sym f-qm↑ ⟩
                                       f qm     ≡⟨ f-qm↓y ⟩∎
                                       just y   ∎))
        (qm≤ pm λ f-pm↑ → ⊎.inj₁≢inj₂ (nothing  ≡⟨ sym f-pm↑ ⟩
                                       f pm     ≡⟨ f-pm↓y ⟩∎
                                       just y   ∎))

  -- All values that a computation can terminate with are equal.

  termination-value-unique :
    ∀ (x : Delay A) {y z} → x ⇓ y → x ⇓ z → y ≡ z
  termination-value-unique (f , inc) {y} {z} (m , fm↓y) (n , fn↓z)
    with N.total m n
  ... | inj₁ m≤n = ⊎.cancel-inj₂
                     (just y  ≡⟨ sym (↓-upwards-closed inc m≤n fm↓y) ⟩
                      f n     ≡⟨ fn↓z ⟩∎
                      just z  ∎)
  ... | inj₂ n≤m = ⊎.cancel-inj₂
                     (just y  ≡⟨ sym fm↓y ⟩
                      f m     ≡⟨ ↓-upwards-closed inc n≤m fn↓z ⟩∎
                      just z  ∎)

  -- _⇓_ is contained in _⇓′_.

  ⇓→⇓′ : ∀ x {y : A} → x ⇓ y → x ⇓′ y
  ⇓→⇓′ x@(f , inc) = uncurry find-min
    where
    find-min : ∀ {y} m → f m ↓ y → x ⇓′ y
    find-min     zero    f0↓y    = zero , f0↓y , λ _ _ → N.zero≤ _
    find-min {y} (suc m) f-1+m↓y with inspect (f m)
    ... | nothing , fm↑ = suc m , f-1+m↓y , 1+m-is-min
      where
      1+m-is-min : ∀ n → ¬ f n ↑ → m N.< n
      1+m-is-min n ¬fn↑ with inspect (f n)
      ... | nothing , fn↑ = ⊥-elim (¬fn↑ fn↑)
      ... | just _  , fn↓ = ↑<↓ inc fm↑ fn↓
    ... | just y′ , fm↓y′ =
               $⟨ find-min m fm↓y′ ⟩
      x ⇓′ y′  ↝⟨ Σ-map id (Σ-map with-other-value id) ⟩□
      x ⇓′ y   □
      where
      with-other-value : ∀ {n} → f n ↓ y′ → f n ↓ y
      with-other-value =
        subst (_ ↓_)
              (termination-value-unique x (_ , fm↓y′) (_ , f-1+m↓y))

  -- _⇓_ and _∥⇓∥_ are pointwise logically equivalent (if A is a set).

  ⇓⇔∥⇓∥ : Is-set A → ∀ x {y : A} → x ⇓ y ⇔ x ∥⇓∥ y
  ⇓⇔∥⇓∥ A-set x {y} = record
    { to   = ∣_∣
    ; from = x ∥⇓∥ y  ↝⟨ Trunc.rec (⇓′-propositional A-set x) (⇓→⇓′ x) ⟩
             x ⇓′ y   ↝⟨ Σ-map id proj₁ ⟩□
             x ⇓ y    □
    }

  -- The notion of termination defined here is logically equivalent
  -- (via Delay⇔Delay) to the one defined for the coinductive delay
  -- monad.

  ⇓⇔⇓ : ∀ {x y} → x ⇓ y ⇔ _⇔_.to Delay⇔Delay x W.⇓ y
  ⇓⇔⇓ = record
    { to   = λ { (n , fn↓y) → to n _ refl fn↓y }
    ; from = from _ refl
    }
    where
    to : ∀ {f : ℕ → Maybe A} {f-inc} n x {y} →
         x ≡ f 0 → f n ↓ y → LE.To.to′ f f-inc x W.⇓ y
    to     (suc n) nothing     f0↑ fn↓y = W.laterʳ (to n _ refl fn↓y)
    to {f} zero    nothing {y} f0↑ fn↓y =
      ⊥-elim $ ⊎.inj₁≢inj₂ (
        nothing  ≡⟨ f0↑ ⟩
        f 0      ≡⟨ fn↓y ⟩∎
        just y   ∎)
    to {f} {f-inc} n (just x) {y} f0↓x fn↓y =
      subst (_ W.⇓_)
            (⊎.cancel-inj₂ {A = ⊤}
               (just x  ≡⟨ sym $ ↓-upwards-closed₀ f-inc (sym f0↓x) n ⟩
                f n     ≡⟨ fn↓y ⟩∎
                just y  ∎))
            W.now-cong

    from : ∀ {f : ℕ → Maybe A} {f-inc y} x →
           x ≡ f 0 → LE.To.to′ f f-inc x W.⇓ y → ∃ λ n → f n ↓ y
    from (just x) f0↓x W.now-cong      = 0 , sym f0↓x
    from nothing  _    (W.laterʳ to⇓y) =
      Σ-map suc id (from _ refl to⇓y)

  ⇓⇔⇓′ : ∀ {x} {y : A} → x W.⇓ y ⇔ _⇔_.from Delay⇔Delay x ⇓ y
  ⇓⇔⇓′ = record
    { to   = to
    ; from = uncurry (from _)
    }
    where
    to : ∀ {x y} → x W.⇓ y → LE.from x ⇓ y
    to W.now-cong   = 0 , refl
    to (W.laterʳ p) = Σ-map suc id (to p)

    from : ∀ x {y} n → proj₁ (LE.from x) n ↓ y → x W.⇓ y
    from (now x)   n       refl = W.now-cong
    from (later x) zero    ()
    from (later x) (suc n) xn↓y = W.laterʳ (from (force x) n xn↓y)

  -- If there is a function f : ℕ → Maybe A satisfying a property
  -- similar to termination-value-unique, then this function can be
  -- turned into a value in Delay A which is, in some sense, weakly
  -- bisimilar to the function.

  complete-function :
    (f : ℕ → Maybe A) →
    (∀ {y z} → (∃ λ m → f m ↓ y) → (∃ λ n → f n ↓ z) → y ≡ z) →
    ∃ λ x → ∀ {y} → x ⇓ y ⇔ ∃ λ n → f n ↓ y
  complete-function f unique =
      (first-value , inc)
    , λ {y} → record
        { to   = (∃ λ n → first-value n ↓ y)  ↝⟨ uncurry first-value↓→f↓ ⟩□
                 (∃ λ n → f n ↓ y)            □
        ; from = (∃ λ n → f n ↓ y)            ↝⟨ Σ-map id (f↓→first-value↓ _) ⟩□
                 (∃ λ n → first-value n ↓ y)  □
        }
    where
    -- If f m terminates for some m smaller than or equal to n, then
    -- first-value n returns the value of f for the largest such m, and
    -- otherwise nothing.

    first-value : ℕ → Maybe A
    first-value zero    = f zero
    first-value (suc n) = [ (λ _ → first-value n) , just ] (f (suc n))

    -- Some simple lemmas.

    step : ∀ {n} → f (suc n) ↑ → first-value (suc n) ≡ first-value n
    step {n} = cong [ (λ _ → first-value n) , just ]

    done : ∀ {n y} → f (suc n) ↓ y → first-value (suc n) ↓ y
    done {n} = cong [ (λ _ → first-value n) , just ]

    -- If f n terminates with a certain value, then first-value n
    -- terminates with the same value.

    f↓→first-value↓ : ∀ {y} n → f n ↓ y → first-value n ↓ y
    f↓→first-value↓ zero    f↓ = f↓
    f↓→first-value↓ (suc n) f↑ = done f↑

    -- If first-value m terminates with a certain value, then there is
    -- some n for which f n terminates with the same value.

    first-value↓→f↓ : ∀ {y} m → first-value m ↓ y → ∃ λ n → f n ↓ y
    first-value↓→f↓     zero    first-value↓ = zero , first-value↓
    first-value↓→f↓ {y} (suc n) first-value↓ with inspect (f (suc n))
    ... | just y′ , f↓ = suc n , (f (suc n)            ≡⟨ f↓ ⟩
                                  just y′              ≡⟨ sym (done f↓) ⟩
                                  first-value (suc n)  ≡⟨ first-value↓ ⟩∎
                                  just y               ∎)
    ... | nothing , f↑ =
      first-value↓→f↓ n (first-value n        ≡⟨ sym (step f↑) ⟩
                         first-value (suc n)  ≡⟨ first-value↓ ⟩∎
                         just y               ∎)

    -- The function first-value is an increasing sequence.

    inc : Increasing first-value
    inc n with inspect (first-value n) | inspect (f (suc n))
    inc n | _ | nothing , f↑ =
      inj₁ (first-value n        ≡⟨ sym (step f↑) ⟩∎
            first-value (suc n)  ∎)
    inc n | nothing , first-value↑ | just y , f↓ =
      inj₂ (first-value↑ , λ first-value↑ → ⊎.inj₁≢inj₂ (
                               nothing              ≡⟨ sym first-value↑ ⟩
                               first-value (suc n)  ≡⟨ done f↓ ⟩∎
                               just y               ∎))
    inc n | just y , first-value↓ | just y′ , f↓ =
      inj₁ (first-value n        ≡⟨ first-value↓ ⟩
            just y               ≡⟨ cong just $ unique (_ , proj₂ (first-value↓→f↓ n first-value↓)) (_ , f↓) ⟩
            just y′              ≡⟨ sym (done f↓) ⟩∎
            first-value (suc n)  ∎)

------------------------------------------------------------------------
-- Information orderings

module _ {a} {A : Set a} where

  infix 4 _⊑_

  -- Information orderings.

  _⊑_ : Delay A → Delay A → Set a
  x ⊑ y = ∀ z → x ⇓ z → y ⇓ z

  _∥⊑∥_ : Delay A → Delay A → Set a
  x ∥⊑∥ y = ∀ z → x ∥⇓∥ z → y ∥⇓∥ z

  -- The two ordering relations are logically equivalent (if A is a
  -- set).

  ⊑⇔∥⊑∥ : Is-set A → ∀ x y → x ⊑ y ⇔ x ∥⊑∥ y
  ⊑⇔∥⊑∥ A-set x y =
    ∀-cong-⇔ λ _ → →-cong-⇔ (⇓⇔∥⇓∥ A-set x) (⇓⇔∥⇓∥ A-set y)

  -- The ordering relation _⊑_ is pointwise logically equivalent (via
  -- Delay⇔Delay) to the ordering relation defined in
  -- Delay-monad.Partial-order.

  ⊑⇔⊑ : ∀ {x y} →
        x ⊑ y ⇔ _⇔_.to Delay⇔Delay x PO.⊑ _⇔_.to Delay⇔Delay y
  ⊑⇔⊑ {x} {y} =
    x ⊑ y                                                              ↝⟨ F.id ⟩
    (∀ z → x ⇓ z → y ⇓ z)                                              ↝⟨ ∀-cong-⇔ (λ _ → →-cong-⇔ ⇓⇔⇓ ⇓⇔⇓) ⟩
    (∀ z → _⇔_.to Delay⇔Delay x  W.⇓ z → _⇔_.to Delay⇔Delay y  W.⇓ z)  ↝⟨ inverse $ ∀-cong-⇔ (λ _ → →-cong-⇔ (_↔_.logical-equivalence PO.⇓↔⇓)
                                                                                                             (_↔_.logical-equivalence PO.⇓↔⇓)) ⟩
    (∀ z → _⇔_.to Delay⇔Delay x PO.⇓ z → _⇔_.to Delay⇔Delay y PO.⇓ z)  ↝⟨ inverse PO.⊑⇔⇓→⇓ ⟩□
    _⇔_.to Delay⇔Delay x PO.⊑ _⇔_.to Delay⇔Delay y                     □

  ⊑⇔⊑′ : ∀ {x y} →
         x PO.⊑ y ⇔ _⇔_.from Delay⇔Delay x ⊑ _⇔_.from Delay⇔Delay y
  ⊑⇔⊑′ {x} {y} =
    x PO.⊑ y                                                         ↝⟨ PO.⊑⇔⇓→⇓ ⟩
    (∀ z → x PO.⇓ z → y PO.⇓ z)                                      ↝⟨ ∀-cong-⇔ (λ _ → →-cong-⇔ (_↔_.logical-equivalence PO.⇓↔⇓)
                                                                                                 (_↔_.logical-equivalence PO.⇓↔⇓))  ⟩
    (∀ z → x  W.⇓ z → y  W.⇓ z)                                      ↝⟨ ∀-cong-⇔ (λ _ → →-cong-⇔ ⇓⇔⇓′ ⇓⇔⇓′) ⟩
    (∀ z → _⇔_.from Delay⇔Delay x ⇓ z → _⇔_.from Delay⇔Delay y ⇓ z)  ↝⟨ F.id ⟩□
    _⇔_.from Delay⇔Delay x ⊑ _⇔_.from Delay⇔Delay y                  □

  -- The ordering relation _∥⊑∥_ is pointwise propositional.

  ∥⊑∥-propositional : ∀ x y → Is-proposition (x ∥⊑∥ y)
  ∥⊑∥-propositional _ _ =
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    truncation-is-proposition

------------------------------------------------------------------------
-- Weak bisimilarity

module _ {a} {A : Set a} where

  infix 4 _≈_

  -- Weak bisimilarity.

  _≈_ : Delay A → Delay A → Set a
  x ≈ y = x ∥⊑∥ y × y ∥⊑∥ x

  -- Weak bisimilarity is pointwise propositional.

  ≈-propositional : ∀ x y → Is-proposition (x ≈ y)
  ≈-propositional x y =
    ×-closure 1 (∥⊑∥-propositional x y) (∥⊑∥-propositional y x)

  -- The notion of weak bisimilarity defined here is logically
  -- equivalent (via Delay⇔Delay) to the one defined for the
  -- coinductive delay monad (if A is a set).

  ≈⇔≈ :
    Is-set A →
    ∀ {x y} → x ≈ y ⇔ _⇔_.to Delay⇔Delay x W.≈ _⇔_.to Delay⇔Delay y
  ≈⇔≈ A-set {x} {y} =
    x ∥⊑∥ y × y ∥⊑∥ x                ↝⟨ inverse (⊑⇔∥⊑∥ A-set x y ×-cong ⊑⇔∥⊑∥ A-set y x) ⟩
    x ⊑ y × y ⊑ x                    ↝⟨ ⊑⇔⊑ ×-cong ⊑⇔⊑ ⟩
    to x PO.⊑ to y × to y PO.⊑ to x  ↝⟨ inverse PO.≈⇔⊑×⊒ ⟩□
    to x W.≈ to y                    □
    where
    open _⇔_ Delay⇔Delay

  ≈⇔≈′ :
    Is-set A →
    ∀ {x y} → x W.≈ y ⇔ _⇔_.from Delay⇔Delay x ≈ _⇔_.from Delay⇔Delay y
  ≈⇔≈′ A-set {x} {y} =
    x W.≈ y                                ↝⟨ PO.≈⇔⊑×⊒ ⟩
    x PO.⊑ y × y PO.⊑ x                    ↝⟨ ⊑⇔⊑′ ×-cong ⊑⇔⊑′ ⟩
    from x ⊑ from y × from y ⊑ from x      ↝⟨ ⊑⇔∥⊑∥ A-set (from x) (from y) ×-cong ⊑⇔∥⊑∥ A-set (from y) (from x) ⟩□
    from x ∥⊑∥ from y × from y ∥⊑∥ from x  □
    where
    open _⇔_ Delay⇔Delay
