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
-- An alternative definition of the delay monad

module _ {a} {A : Set a} where

  -- x ↑ means that the computation x does not have a value.

  infix 4 _↑

  _↑ : Maybe A → Set a
  x ↑ = x ≡ nothing

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
-- Auxiliary definitions and lemmas

module _ {a} {A : Set a} where

  -- x ↓ y means that the computation x terminates with the value y.

  infix 4 _↓_

  _↓_ : Maybe A → A → Set a
  x ↓ y = x ≡ just y

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

private

  -- If f is increasing and f 0 terminates, then f 1 terminates.

  step : ∀ {a} {A : Set a} {f} {x : A} →
         Increasing f → f 0 ↓ x → f 1 ↓ x
  step {f = f} {x} inc f0↓x = step′ (inc 0)
    module Step where
    step′ : LE (f 0) (f 1) → f 1 ↓ x
    step′ (inj₁ f0≡f1) =

      f 1     ≡⟨ sym f0≡f1 ⟩
      f 0     ≡⟨ f0↓x ⟩∎
      just x  ∎

    step′ (inj₂ (f0↑ , f1↓)) =

      ⊥-elim $ ⊎.inj₁≢inj₂ (
        nothing  ≡⟨ sym f0↑ ⟩
        f 0      ≡⟨ f0↓x ⟩∎
        just x   ∎)

-- If f is increasing and f 0 terminates, then f n terminates.

upwards-closed₀ : ∀ {a} {A : Set a} {f} {x : A} →
                  Increasing f → f 0 ↓ x → ∀ n → f n ↓ x
upwards-closed₀ _   f0↓ zero    = f0↓
upwards-closed₀ inc f0↓ (suc n) =
  upwards-closed₀ (inc ∘ suc) (step inc f0↓) n

------------------------------------------------------------------------
-- Theorems relating the two definitions of the delay monad

module _ {a} {A : Set a} where

  -- The two definitions are logically equivalent.

  private

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

  Delay⇔Delay : Delay A ⇔ D.Delay A ∞
  Delay⇔Delay = record { to = to; from = from }

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
      proj₁∘from∘to g g-inc (just x) g0↓x n       = sym $ upwards-closed₀ g-inc g0↓x n
      proj₁∘from∘to g g-inc nothing  g0↑  zero    = sym g0↑
      proj₁∘from∘to g g-inc nothing  g0↑  (suc n) =
          proj₁∘from∘to (g ∘ suc) (g-inc ∘ suc) _ refl n

      ↓-lemma :
        (g : ℕ → Maybe A) →
        (g-increasing : Increasing g) →
        ∀ n x (g0↓x : g 0 ↓ x) p → p ≡ g-increasing 0 →

        subst (Increasing-at n)
              (ext (sym ∘ upwards-closed₀ g-increasing g0↓x))
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
              (ext (sym ∘ upwards-closed₀ g-inc g0↓x))
              (inj₁ refl)                                     ≡⟨ push-subst-inj₁
                                                                   {y≡z = ext (sym ∘ upwards-closed₀ g-inc g0↓x)}
                                                                   (λ f → f 0 ≡ f 1) (λ f → f 0 ↑ × ¬ f 1 ↑) ⟩
        inj₁ (subst (λ f → f 0 ≡ f 1)
                    (ext (sym ∘ upwards-closed₀ g-inc g0↓x))
                    refl)                                     ≡⟨ cong inj₁ lemma ⟩

        inj₁ g0≡g1                                            ≡⟨ ≡g-inc0 ⟩∎

        g-inc zero                                            ∎

        where
        eq    = upwards-closed₀ g-inc g0↓x
        lemma =

          subst (λ f → f 0 ≡ f 1) (ext (sym ∘ eq)) refl          ≡⟨ subst-in-terms-of-trans-and-cong {x≡y = ext (sym ∘ eq)} ⟩

          trans (sym (cong (_$ 0) (ext (sym ∘ eq))))
                (trans refl (cong (_$ 1) (ext (sym ∘ eq))))      ≡⟨ cong (trans (sym (cong (_$ 0) (ext (sym ∘ eq))))) $
                                                                      trans-reflˡ (cong (_$ 1) (ext (sym ∘ eq))) ⟩
          trans (sym (cong (_$ 0) (ext (sym ∘ eq))))
                (cong (_$ 1) (ext (sym ∘ eq)))                   ≡⟨ cong₂ (λ p q → trans (sym p) q) (cong-ext (sym ∘ eq)) (cong-ext (sym ∘ eq)) ⟩

          trans (sym $ sym $ eq 0) (sym $ eq 1)                  ≡⟨ cong (λ eq′ → trans eq′ (sym $ eq 1)) $ sym-sym _ ⟩

          trans (eq 0) (sym $ eq 1)                              ≡⟨⟩

          trans g0↓x (sym $ Step.step′ g-inc g0↓x (g-inc 0))     ≡⟨ cong (λ eq′ → trans g0↓x (sym $ Step.step′ g-inc g0↓x eq′)) $ sym $ ≡g-inc0 ⟩

          trans g0↓x (sym $ Step.step′ g-inc g0↓x (inj₁ g0≡g1))  ≡⟨⟩

          trans g0↓x (sym $ trans (sym g0≡g1) g0↓x)              ≡⟨ cong (trans g0↓x) $ sym-trans (sym g0≡g1) g0↓x ⟩

          trans g0↓x (trans (sym g0↓x) (sym (sym g0≡g1)))        ≡⟨ trans--[trans-sym] _ _ ⟩

          sym (sym g0≡g1)                                        ≡⟨ sym-sym _ ⟩∎

          g0≡g1                                                  ∎

      ↓-lemma g g-inc (suc n) x g0↓x (inj₁ g0≡g1) ≡g-inc0 =

        subst (Increasing-at (suc n))
              (ext (sym ∘ upwards-closed₀ g-inc g0↓x))
              (inj₁ refl)                                                 ≡⟨⟩

        subst (Increasing-at n ∘ (_∘ suc))
              (ext (sym ∘ upwards-closed₀ g-inc g0↓x))
              (inj₁ refl)                                                 ≡⟨ subst-∘ (Increasing-at n) (_∘ suc)
                                                                                     (ext (sym ∘ upwards-closed₀ g-inc g0↓x)) ⟩
        subst (Increasing-at n)
              (cong (_∘ suc)
                 (ext (sym ∘ upwards-closed₀ g-inc g0↓x)))
              (inj₁ refl)                                                 ≡⟨ cong (λ eq → subst (Increasing-at n) eq _) $
                                                                               cong-∘-ext (sym ∘ upwards-closed₀ g-inc g0↓x) ⟩
        subst (Increasing-at n)
              (ext (sym ∘ upwards-closed₀ g-inc g0↓x ∘ suc))
              (inj₁ refl)                                                 ≡⟨⟩

        subst (Increasing-at n)
              (ext (sym ∘ upwards-closed₀ (g-inc ∘ suc)
                            (Step.step′ g-inc g0↓x (g-inc 0))))
              (inj₁ refl)                                                 ≡⟨ cong (λ p → subst (Increasing-at n)
                                                                                               (ext (sym ∘ upwards-closed₀ (g-inc ∘ suc)
                                                                                                             (Step.step′ g-inc g0↓x p)))
                                                                                               (inj₁ refl))
                                                                                  (sym ≡g-inc0) ⟩
        subst (Increasing-at n)
              (ext (sym ∘ upwards-closed₀ (g-inc ∘ suc)
                            (Step.step′ g-inc g0↓x (inj₁ g0≡g1))))
              (inj₁ refl)                                                 ≡⟨⟩

        subst (Increasing-at n)
              (ext (sym ∘ upwards-closed₀ (g-inc ∘ suc)
                                          (trans (sym g0≡g1) g0↓x)))
              (inj₁ refl)                                                 ≡⟨ ↓-lemma (g ∘ suc) (g-inc ∘ suc) n _ _ _ refl ⟩∎

        g-inc (suc n)                                                     ∎

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
-- Weak bisimilarity

module _ {a} {A : Set a} where

  infix 4 _⇓_ _⊑_ _≈_

  -- x ⇓ y means that the computation x terminates with the value y.

  _⇓_ : Delay A → A → Set a
  (f , _) ⇓ y = ∃ λ n → f n ↓ y

  -- Information ordering.

  _⊑_ : Delay A → Delay A → Set a
  x ⊑ y = ∀ z → x ⇓ z → y ⇓ z

  -- Weak bisimilarity.

  _≈_ : Delay A → Delay A → Set a
  x ≈ y = x ⊑ y × y ⊑ x

  -- The notion of termination defined here is logically equivalent
  -- (via Delay⇔Delay) to the one defined for the coinductive delay
  -- monad.

  ⇓⇔⇓ : ∀ {x y} → x ⇓ y ⇔ _⇔_.to Delay⇔Delay x W.⇓ y
  ⇓⇔⇓ = record
    { to   = λ { (n , fn↓y) → to′ n _ refl fn↓y }
    ; from = from′ _ refl
    }
    where
    to′ : ∀ {f : ℕ → Maybe A} {f-inc} n x {y} →
          x ≡ f 0 → f n ↓ y → To.to′ f f-inc x W.⇓ y
    to′     (suc n) nothing     f0↑ fn↓y = W.laterʳ (to′ n _ refl fn↓y)
    to′ {f} zero    nothing {y} f0↑ fn↓y =
      ⊥-elim $ ⊎.inj₁≢inj₂ (
        nothing  ≡⟨ f0↑ ⟩
        f 0      ≡⟨ fn↓y ⟩∎
        just y   ∎)
    to′ {f} {f-inc} n (just x) {y} f0↓x fn↓y =
      subst (_ W.⇓_)
            (⊎.cancel-inj₂ {A = ⊤}
               (just x  ≡⟨ sym $ upwards-closed₀ f-inc (sym f0↓x) n ⟩
                f n     ≡⟨ fn↓y ⟩∎
                just y  ∎))
            W.now-cong

    from′ : ∀ {f : ℕ → Maybe A} {f-inc y} x →
            x ≡ f 0 → To.to′ f f-inc x W.⇓ y → ∃ λ n → f n ↓ y
    from′ (just x) f0↓x W.now-cong      = 0 , sym f0↓x
    from′ nothing  _    (W.laterʳ to⇓y) =
      Σ-map suc id (from′ _ refl to⇓y)

  -- The ordering relation defined here is logically equivalent (via
  -- Delay⇔Delay) to the one defined in Delay-monad.Partial-order.

  ⊑⇔⊑ : ∀ {x y} →
        x ⊑ y ⇔ _⇔_.to Delay⇔Delay x PO.⊑ _⇔_.to Delay⇔Delay y
  ⊑⇔⊑ {x} {y} =
    x ⊑ y                                                              ↝⟨ F.id ⟩
    (∀ z → x ⇓ z → y ⇓ z)                                              ↝⟨ ∀-cong-⇔ (λ _ → →-cong-⇔ ⇓⇔⇓ ⇓⇔⇓) ⟩
    (∀ z → _⇔_.to Delay⇔Delay x  W.⇓ z → _⇔_.to Delay⇔Delay y  W.⇓ z)  ↝⟨ inverse $ ∀-cong-⇔ (λ _ → →-cong-⇔ (_↔_.logical-equivalence PO.⇓↔⇓)
                                                                                                             (_↔_.logical-equivalence PO.⇓↔⇓)) ⟩
    (∀ z → _⇔_.to Delay⇔Delay x PO.⇓ z → _⇔_.to Delay⇔Delay y PO.⇓ z)  ↝⟨ inverse PO.⊑⇔⇓→⇓ ⟩□
    _⇔_.to Delay⇔Delay x PO.⊑ _⇔_.to Delay⇔Delay y                     □

  -- The notion of weak bisimilarity defined here is logically
  -- equivalent (via Delay⇔Delay) to the one defined for the
  -- coinductive delay monad.

  ≈⇔≈ : ∀ {x y} →
        x ≈ y ⇔ _⇔_.to Delay⇔Delay x W.≈ _⇔_.to Delay⇔Delay y
  ≈⇔≈ {x} {y} =
    x ⊑ y × y ⊑ x                    ↝⟨ ⊑⇔⊑ ×-cong ⊑⇔⊑ ⟩
    to x PO.⊑ to y × to y PO.⊑ to x  ↝⟨ inverse PO.≈⇔⊑×⊒ ⟩□
    to x W.≈ to y                    □
    where
    open _⇔_ Delay⇔Delay
