------------------------------------------------------------------------
-- An alternative definition of the delay monad
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad.Alternative where

open import Equality.Propositional
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
import Nat equality-with-J as N
open import Surjection equality-with-J using (_↠_)

open import Delay-monad as D using (now; later; force)
open import Delay-monad.Strong-bisimilarity as S
  using (_∼_; _∞∼_; now-cong; later-cong; force)

-- An alternative definition of N._≤_.

infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where
  zero≤   : ∀ n → zero ≤ n
  suc≤suc : ∀ {m n} → m ≤ n → suc m ≤ suc n

-- x ⇓ y means that the computation x terminates with the value y.

_⇓_ : ∀ {a} {A : Set a} → Maybe A → A → Set a
x ⇓ y = just y ≡ x

-- Upwards closed with respect to _⇓_.

Upwards-closed : ∀ {a} {A : Set a} → (ℕ → Maybe A) → Set a
Upwards-closed f = ∀ {m n x} → m ≤ n → f m ⇓ x → f n ⇓ x

-- An alternative definition of the delay monad. Nicolai Kraus
-- suggested a similar definition.

Delay : ∀ {a} → Set a → Set a
Delay A = ∃ λ (f : ℕ → Maybe A) → Upwards-closed f

module _ {a} {A : Set a} where

  -- The two definitions are logically equivalent.

  private

    to : Delay A → D.Delay A ∞
    to (f , upwards-closed) = to′ (f 0)
      module To where
      mutual

        to′ : Maybe A → D.Delay A ∞
        to′ (just x) = now x
        to′ nothing  =
          later (∞to (f ∘ suc , upwards-closed ∘ suc≤suc))

        ∞to : Delay A → D.∞Delay A ∞
        force (∞to x) = to x

    from : D.Delay A ∞ → Delay A
    from = λ x → f x , f-upwards-closed x
      where
      f : D.Delay A ∞ → ℕ → Maybe A
      f (now x)   _       = just x
      f (later x) zero    = nothing
      f (later x) (suc n) = f (force x) n

      f-upwards-closed : ∀ x → Upwards-closed (f x)
      f-upwards-closed (now x)   _            = id
      f-upwards-closed (inj₂ x) (zero≤ n) ()
      f-upwards-closed (inj₂ x) (suc≤suc m≤n) =
        f-upwards-closed (force x) m≤n

  Delay⇔Delay : Delay A ⇔ D.Delay A ∞
  Delay⇔Delay = record { to = to; from = from }

  -- There is a split surjection from the alternative definition to
  -- the other one (assuming extensionality).

  Delay↠Delay : S.Extensionality a →
                Delay A ↠ D.Delay A ∞
  Delay↠Delay delay-ext = record
    { logical-equivalence = Delay⇔Delay
    ; right-inverse-of    = delay-ext ∘ to∘from
    }
    where
    mutual

      to∘from : ∀ x → to (from x) ∼ x
      to∘from (now x)   = now-cong
      to∘from (later x) = later-cong (∞to∘from (force x))

      ∞to∘from : ∀ x → to (from x) ∞∼ x
      force (∞to∘from x) = to∘from x

  -- If A is a set, then the two definitions are isomorphic
  -- (assuming extensionality).

  Delay↔Delay : S.Extensionality a →
                Is-set A →
                Delay A ↔ D.Delay A ∞
  Delay↔Delay delay-ext A-set = record
    { surjection      = Delay↠Delay delay-ext
    ; left-inverse-of = from∘to
    }
    where
    proj₁∘from∘to :
      (g : ℕ → Maybe A) →
      (g-upwards-closed : Upwards-closed g) →
      ∀ n → proj₁ (from (to (g , g-upwards-closed))) n ≡ g n
    proj₁∘from∘to g g-upwards-closed n = lemma _ refl n
      where
      lemma : ∀ x → x ≡ g 0 →
              ∀ n → proj₁ (from (To.to′ g g-upwards-closed x)) n ≡ g n
      lemma (just x) g0⇓x n       = g-upwards-closed (zero≤ n) g0⇓x
      lemma nothing  g0⇑  zero    = g0⇑
      lemma nothing  g0⇑  (suc n) =
        proj₁∘from∘to (g ∘ suc) (g-upwards-closed ∘ suc≤suc) n

    from∘to : ∀ x → from (to x) ≡ x
    from∘to (g , g-upwards-closed) = Σ-≡,≡→≡
      (ext (proj₁∘from∘to g g-upwards-closed))
      (_⇔_.to propositional⇔irrelevant
         (implicit-Π-closure ext 1 λ _ →
          implicit-Π-closure ext 1 λ _ →
          implicit-Π-closure ext 1 λ _ →
          Π-closure ext 1 λ _ →
          Π-closure ext 1 λ _ →
          ⊎-closure 0 (mono (N.zero≤ 2) ⊤-contractible)
                      A-set
                      _ _)
         _ _)
