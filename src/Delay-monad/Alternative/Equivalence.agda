------------------------------------------------------------------------
-- Theorems relating the coinductive definition of the delay
-- monad to the alternative one and to another type
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe --sized-types #-}

module Delay-monad.Alternative.Equivalence {a} {A : Set a} where

open import Equality.Propositional.Cubical
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (↑)
open import Prelude.Size

open import Bijection equality-with-J using (_↔_)
open import Equality.Decision-procedures equality-with-J
open import Function-universe equality-with-J hiding (_∘_)
open import H-level equality-with-J
open import Surjection equality-with-J using (_↠_)

open import Delay-monad as D hiding (Delay)
open import Delay-monad.Alternative
open import Delay-monad.Alternative.Properties
open import Delay-monad.Bisimilarity as Bisimilarity
  using ([_]_∼_; now; later; force)

private
  variable
    i : Size

-- Building blocks used in the theorems below.

module Delay⇔Delay where

  -- The function to₁ is basically π from Section 7.1 of
  -- "Quotienting the Delay Monad by Weak Bisimilarity" by Chapman,
  -- Uustalu and Veltri, but the function proj₁ ∘ from is different
  -- from their function ε, which is defined so that (with the
  -- terminology used here) ε (now x) (suc n) = nothing.

  to₁ : (ℕ → Maybe A) → D.Delay A i
  to₁ f = to′ (f 0)
    module To where
    to′ : Maybe A → D.Delay A i
    to′ (just x) = now x
    to′ nothing  =
      later λ { .force → to₁ (f ∘ suc) }

  to : Delay A → D.Delay A i
  to = to₁ ∘ proj₁

  from : D.Delay A ∞ → Delay A
  from = λ x → from₁ x , from₂ x
    where
    from₁ : D.Delay A ∞ → ℕ → Maybe A
    from₁ (now x)   _       = just x
    from₁ (later x) zero    = nothing
    from₁ (later x) (suc n) = from₁ (force x) n

    from₂ : ∀ x → Increasing (from₁ x)
    from₂ (now x)   _       = inj₁ refl
    from₂ (later x) zero    = proj₁ LE-nothing-contractible
    from₂ (later x) (suc n) = from₂ (force x) n

-- The two definitions of the delay monad are logically equivalent.

Delay⇔Delay : Delay A ⇔ D.Delay A ∞
Delay⇔Delay = record { to = Delay⇔Delay.to; from = Delay⇔Delay.from }

-- There is a split surjection from D.Delay A ∞ to Delay A.

Delay↠Delay : D.Delay A ∞ ↠ Delay A
Delay↠Delay = record
  { logical-equivalence = inverse Delay⇔Delay
  ; right-inverse-of    = from∘to
  }
  where
  open Delay⇔Delay

  from∘to : ∀ x → from (to x) ≡ x
  from∘to x = Σ-≡,≡→≡
    (⟨ext⟩ (proj₁∘from∘to x))
    (⟨ext⟩ λ n →

       subst Increasing
             (⟨ext⟩ (proj₁∘from∘to x))
             (proj₂ (from (to x)))
             n                          ≡⟨ sym $ push-subst-application (⟨ext⟩ (proj₁∘from∘to x)) (flip Increasing-at) ⟩

       subst (Increasing-at n)
             (⟨ext⟩ (proj₁∘from∘to x))
             (proj₂ (from (to x)) n)    ≡⟨ uncurry proj₂∘from∘to x n _ refl ⟩∎

       proj₂ x n                        ∎)

    where

    proj₁∘from∘to′ :
      (g : ℕ → Maybe A) →
      Increasing g →
      ∀ x → g 0 ≡ x → ∀ n →
      proj₁ (from (To.to′ g x)) n ≡ g n
    proj₁∘from∘to′ g g-inc (just x) g0↓x n       = sym $ ↓-upwards-closed₀ g-inc g0↓x n
    proj₁∘from∘to′ g g-inc nothing  g0↑  zero    = sym g0↑
    proj₁∘from∘to′ g g-inc nothing  g0↑  (suc n) =
        proj₁∘from∘to′ (g ∘ suc) (g-inc ∘ suc) _ refl n

    proj₁∘from∘to :
      (x : Delay A) →
      ∀ n → proj₁ (from (to x)) n ≡ proj₁ x n
    proj₁∘from∘to (g , g-inc) = proj₁∘from∘to′ g g-inc (g 0) refl

    ↓-lemma :
      (g : ℕ → Maybe A) →
      (g-increasing : Increasing g) →
      ∀ n x (g0↓x : g 0 ↓ x) p → p ≡ g-increasing 0 →

      subst (Increasing-at n)
            (⟨ext⟩ (sym ∘ ↓-upwards-closed₀ g-increasing g0↓x))
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
            (⟨ext⟩ (sym ∘ ↓-upwards-closed₀ g-inc g0↓x))
            (inj₁ refl)                                         ≡⟨ push-subst-inj₁
                                                                     {y≡z = ⟨ext⟩ (sym ∘ ↓-upwards-closed₀ g-inc g0↓x)}
                                                                     (λ f → f 0 ≡ f 1) (λ f → f 0 ↑ × ¬ f 1 ↑) ⟩
      inj₁ (subst (λ f → f 0 ≡ f 1)
                  (⟨ext⟩ (sym ∘ ↓-upwards-closed₀ g-inc g0↓x))
                  refl)                                         ≡⟨ cong inj₁ lemma ⟩

      inj₁ g0≡g1                                                ≡⟨ ≡g-inc0 ⟩∎

      g-inc zero                                                ∎

      where
      eq    = ↓-upwards-closed₀ g-inc g0↓x
      lemma =

        subst (λ f → f 0 ≡ f 1) (⟨ext⟩ (sym ∘ eq)) refl      ≡⟨ subst-in-terms-of-trans-and-cong {x≡y = ⟨ext⟩ (sym ∘ eq)} ⟩

        trans (sym (cong (_$ 0) (⟨ext⟩ (sym ∘ eq))))
              (trans refl (cong (_$ 1) (⟨ext⟩ (sym ∘ eq))))  ≡⟨ cong (trans (sym (cong (_$ 0) (⟨ext⟩ (sym ∘ eq))))) $
                                                                  trans-reflˡ (cong (_$ 1) (⟨ext⟩ (sym ∘ eq))) ⟩
        trans (sym (cong (_$ 0) (⟨ext⟩ (sym ∘ eq))))
              (cong (_$ 1) (⟨ext⟩ (sym ∘ eq)))               ≡⟨ cong₂ (λ p q → trans (sym p) q) (cong-ext (sym ∘ eq)) (cong-ext (sym ∘ eq)) ⟩

        trans (sym $ sym $ eq 0) (sym $ eq 1)                ≡⟨ cong (λ eq′ → trans eq′ (sym $ eq 1)) $ sym-sym _ ⟩

        trans (eq 0) (sym $ eq 1)                            ≡⟨⟩

        trans g0↓x (sym $ ↓.step g-inc g0↓x (g-inc 0))       ≡⟨ cong (λ eq′ → trans g0↓x (sym $ ↓.step g-inc g0↓x eq′)) $ sym $ ≡g-inc0 ⟩

        trans g0↓x (sym $ ↓.step g-inc g0↓x (inj₁ g0≡g1))    ≡⟨⟩

        trans g0↓x (sym $ trans (sym g0≡g1) g0↓x)            ≡⟨ cong (trans g0↓x) $ sym-trans (sym g0≡g1) g0↓x ⟩

        trans g0↓x (trans (sym g0↓x) (sym (sym g0≡g1)))      ≡⟨ trans--[trans-sym] _ _ ⟩

        sym (sym g0≡g1)                                      ≡⟨ sym-sym _ ⟩∎

        g0≡g1                                                ∎

    ↓-lemma g g-inc (suc n) x g0↓x (inj₁ g0≡g1) ≡g-inc0 =

      subst (Increasing-at (suc n))
            (⟨ext⟩ (sym ∘ ↓-upwards-closed₀ g-inc g0↓x))
            (inj₁ refl)                                                   ≡⟨⟩

      subst (Increasing-at n ∘ (_∘ suc))
            (⟨ext⟩ (sym ∘ ↓-upwards-closed₀ g-inc g0↓x))
            (inj₁ refl)                                                   ≡⟨ subst-∘ (Increasing-at n) (_∘ suc)
                                                                                     (⟨ext⟩ (sym ∘ ↓-upwards-closed₀ g-inc g0↓x)) ⟩
      subst (Increasing-at n)
            (cong (_∘ suc) (⟨ext⟩ (sym ∘ ↓-upwards-closed₀ g-inc g0↓x)))
            (inj₁ refl)                                                   ≡⟨ cong (λ eq → subst (Increasing-at n) eq _) $
                                                                               cong-pre-∘-ext (sym ∘ ↓-upwards-closed₀ g-inc g0↓x) ⟩
      subst (Increasing-at n)
            (⟨ext⟩ (sym ∘ ↓-upwards-closed₀ g-inc g0↓x ∘ suc))
            (inj₁ refl)                                                   ≡⟨⟩

      subst (Increasing-at n)
            (⟨ext⟩ (sym ∘ ↓-upwards-closed₀ (g-inc ∘ suc)
                            (↓.step g-inc g0↓x (g-inc 0))))
            (inj₁ refl)                                                   ≡⟨ cong (λ p → subst (Increasing-at n)
                                                                                               (⟨ext⟩ (sym ∘ ↓-upwards-closed₀ (g-inc ∘ suc)
                                                                                                               (↓.step g-inc g0↓x p)))
                                                                                               (inj₁ refl))
                                                                                  (sym ≡g-inc0) ⟩
      subst (Increasing-at n)
            (⟨ext⟩ (sym ∘ ↓-upwards-closed₀ (g-inc ∘ suc)
                            (↓.step g-inc g0↓x (inj₁ g0≡g1))))
            (inj₁ refl)                                                   ≡⟨⟩

      subst (Increasing-at n)
            (⟨ext⟩ (sym ∘ ↓-upwards-closed₀ (g-inc ∘ suc)
                            (trans (sym g0≡g1) g0↓x)))
            (inj₁ refl)                                                   ≡⟨ ↓-lemma (g ∘ suc) (g-inc ∘ suc) n _ _ _ refl ⟩∎

      g-inc (suc n)                                                       ∎

    proj₂∘from∘to :
      (g : ℕ → Maybe A) →
      (g-increasing : Increasing g) →
      ∀ n y (g0≡y : g 0 ≡ y) →

      subst (Increasing-at n)
            (⟨ext⟩ (proj₁∘from∘to′ g g-increasing y g0≡y))
            (proj₂ (from (To.to′ g y)) n)
        ≡
      g-increasing n

    proj₂∘from∘to g g-inc n (just y) g0↓y =
      ↓-lemma g g-inc n y g0↓y _ refl

    proj₂∘from∘to g g-inc zero nothing g0↑ =
      (                                   $⟨ mono₁ 0 LE-nothing-contractible ⟩
       Is-proposition (LE nothing (g 1))  ↝⟨ subst (λ x → Is-proposition (LE x (g 1))) (sym g0↑) ⟩□
       Is-proposition (LE (g 0) (g 1))    □) _ _

    proj₂∘from∘to g g-inc (suc n) nothing g0↑ =

      subst (Increasing-at (suc n))
            (⟨ext⟩ (proj₁∘from∘to′ g g-inc nothing g0↑))
            (proj₂ (from (to (g ∘ suc , g-inc ∘ suc))) n)                 ≡⟨⟩

      subst (Increasing-at n ∘ (_∘ suc))
            (⟨ext⟩ (proj₁∘from∘to′ g g-inc nothing g0↑))
            (proj₂ (from (to (g ∘ suc , g-inc ∘ suc))) n)                 ≡⟨ subst-∘ (Increasing-at n) (_∘ suc)
                                                                                     (⟨ext⟩ (proj₁∘from∘to′ g g-inc nothing g0↑)) ⟩
      subst (Increasing-at n)
            (cong (_∘ suc) (⟨ext⟩ (proj₁∘from∘to′ g g-inc nothing g0↑)))
            (proj₂ (from (to (g ∘ suc , g-inc ∘ suc))) n)                 ≡⟨ cong (λ eq → subst (Increasing-at n) eq
                                                                                                (proj₂ (from (to (g ∘ suc , g-inc ∘ suc))) n)) $
                                                                               cong-pre-∘-ext (proj₁∘from∘to′ g g-inc nothing g0↑) ⟩
      subst (Increasing-at n)
            (⟨ext⟩ (proj₁∘from∘to′ g g-inc nothing g0↑ ∘ suc))
            (proj₂ (from (to (g ∘ suc , g-inc ∘ suc))) n)                 ≡⟨⟩

      subst (Increasing-at n)
            (⟨ext⟩ (proj₁∘from∘to′ (g ∘ suc) (g-inc ∘ suc) _ refl))
            (proj₂ (from (to (g ∘ suc , g-inc ∘ suc))) n)                 ≡⟨ proj₂∘from∘to (g ∘ suc) (g-inc ∘ suc) n _ refl ⟩∎

      g-inc (suc n)                                                       ∎

-- The two definitions of the delay monad are isomorphic (assuming
-- extensionality).

Delay↔Delay : Bisimilarity.Extensionality a →
              Delay A ↔ D.Delay A ∞
Delay↔Delay delay-ext = record
  { surjection = record
    { logical-equivalence = Delay⇔Delay
    ; right-inverse-of    = delay-ext ∘ to∘from
    }
  ; left-inverse-of = _↠_.right-inverse-of Delay↠Delay
  }
  where
  open Delay⇔Delay

  to∘from : ∀ x → [ i ] to (from x) ∼ x
  to∘from (now x)   = now
  to∘from (later x) = later λ { .force → to∘from (force x) }

-- There is a split surjection from ℕ → Maybe A (without any
-- requirement that the sequences are increasing) to D.Delay A ∞
-- (assuming extensionality).
--
-- Chapman, Uustalu and Veltri prove this result in "Quotienting the
-- Delay Monad by Weak Bisimilarity".

→↠Delay-coinductive : Bisimilarity.Extensionality a →
                      (ℕ → Maybe A) ↠ D.Delay A ∞
→↠Delay-coinductive delay-ext = record
  { logical-equivalence = record
    { to   = Delay⇔Delay.to₁
    ; from = proj₁ ∘ Delay⇔Delay.from
    }
  ; right-inverse-of = _↔_.right-inverse-of (Delay↔Delay delay-ext)
  }

-- There is also a split surjection from ℕ → Maybe A to Delay A.

→↠Delay-function : (ℕ → Maybe A) ↠ Delay A
→↠Delay-function = record
  { logical-equivalence = record
    { to   = Delay⇔Delay.from ∘ Delay⇔Delay.to₁
    ; from = proj₁
    }
  ; right-inverse-of = _↠_.right-inverse-of Delay↠Delay
  }
