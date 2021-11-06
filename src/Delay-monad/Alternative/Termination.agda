------------------------------------------------------------------------
-- Termination predicates
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --sized-types #-}

open import Prelude hiding (↑; module W)

module Delay-monad.Alternative.Termination {a} {A : Type a} where

open import Equality.Propositional.Cubical
open import Logical-equivalence using (_⇔_)

open import Equality.Decision-procedures equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-paths
  as Trunc
import Nat equality-with-J as N

open import Delay-monad hiding (Delay)
open import Delay-monad.Alternative
open import Delay-monad.Alternative.Equivalence
open import Delay-monad.Alternative.Properties
import Delay-monad.Bisimilarity as B
import Delay-monad.Termination as T

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

_⇓_ : Delay A → A → Type a
(f , _) ⇓ y = ∃ λ n → f n ↓ y

_∥⇓∥_ : Delay A → A → Type a
x ∥⇓∥ y = ∥ x ⇓ y ∥

_⇓′_ : Delay A → A → Type _
(f , _) ⇓′ y = ∃ λ m → f m ↓ y × (∀ n → ¬ f n ↑ → m N.≤ n)

-- _⇓′_ is a family of propositions (if A is a set).

⇓′-propositional :
  Is-set A → ∀ x {y : A} → Is-proposition (x ⇓′ y)
⇓′-propositional A-set x@(f , _) {y} p q =
                     $⟨ number-unique p q ⟩
  proj₁ p ≡ proj₁ q  ↝⟨ ignore-propositional-component
                          (×-closure 1 (Maybe-closure 0 A-set)
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

⇓⇔⇓ : ∀ x {y} → x ⇓ y ⇔ _⇔_.to Delay⇔Delay x T.⇓ y
⇓⇔⇓ x = record
  { to   = λ { (n , fn↓y) → to n _ (proj₂ x) refl fn↓y }
  ; from = from _ refl
  }
  where
  to : ∀ {f : ℕ → Maybe A} n x {y} →
       Increasing f →
       x ≡ f 0 → f n ↓ y → Delay⇔Delay.To.to′ f x T.⇓ y
  to (suc n) nothing f-inc f0↑ fn↓y =
    B.laterʳ (to n _ (f-inc ∘ suc) refl fn↓y)

  to {f} zero nothing {y} _ f0↑ fn↓y =
    ⊥-elim $ ⊎.inj₁≢inj₂ (
      nothing  ≡⟨ f0↑ ⟩
      f 0      ≡⟨ fn↓y ⟩∎
      just y   ∎)

  to {f} n (just x) {y} f-inc f0↓x fn↓y =
    subst (_ T.⇓_)
          (⊎.cancel-inj₂ {A = ⊤}
             (just x  ≡⟨ sym $ ↓-upwards-closed₀ f-inc (sym f0↓x) n ⟩
              f n     ≡⟨ fn↓y ⟩∎
              just y  ∎))
          B.now

  from : ∀ {f : ℕ → Maybe A} {y} x →
         x ≡ f 0 → Delay⇔Delay.To.to′ f x T.⇓ y → ∃ λ n → f n ↓ y
  from (just x) f0↓x B.now           = 0 , sym f0↓x
  from nothing  _    (B.laterʳ to⇓y) =
    Σ-map suc id (from _ refl to⇓y)

⇓⇔⇓′ : ∀ {x} {y : A} → x T.⇓ y ⇔ _⇔_.from Delay⇔Delay x ⇓ y
⇓⇔⇓′ = record
  { to   = to
  ; from = uncurry (from _)
  }
  where
  to : ∀ {x y} → x T.⇓ y → Delay⇔Delay.from x ⇓ y
  to B.now        = 0 , refl
  to (B.laterʳ p) = Σ-map suc id (to p)

  from : ∀ x {y} n → proj₁ (Delay⇔Delay.from x) n ↓ y → x T.⇓ y
  from (now x)   n       refl = B.now
  from (later x) zero    ()
  from (later x) (suc n) xn↓y = B.laterʳ (from (force x) n xn↓y)

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
  first-value (suc n) =
    Prelude.[ (λ _ → first-value n) , just ] (f (suc n))

  -- Some simple lemmas.

  step : ∀ {n} → f (suc n) ↑ → first-value (suc n) ≡ first-value n
  step {n} = cong Prelude.[ (λ _ → first-value n) , just ]

  done : ∀ {n y} → f (suc n) ↓ y → first-value (suc n) ↓ y
  done {n} = cong Prelude.[ (λ _ → first-value n) , just ]

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
