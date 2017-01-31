------------------------------------------------------------------------
-- An alternative definition of the delay monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --rewriting #-}

module Delay-monad.Alternative where

open import Equality.Propositional
open import H-level.Truncation.Propositional as Trunc
open import Interval
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (↑; module W)
open import Quotient.HIT as Quotient

open import Bijection equality-with-J as Bijection using (_↔_)
open import Embedding equality-with-J as Embedding using (Embedding)
open import Equality.Decision-procedures equality-with-J
import Equality.Groupoid equality-with-J as EG
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import Groupoid equality-with-J
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import Injection equality-with-J using (Injective)
import Nat equality-with-J as N
import Quotient equality-with-J as Quotient′
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

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

-- Pointwise lifting of binary relations to the delay monad.

Delayᴾ :
  ∀ {a r} {A : Set a} →
  (A → A → Proposition r) →
  Delay A → Delay A → Proposition r
Delayᴾ R = (ℕ →ᴾ Maybeᴾ R) on proj₁

------------------------------------------------------------------------
-- A map function

private

  module _ {a b} {A : Set a} {B : Set b} where

    -- A map function for Maybe.

    mapᴹ : (A → B) → Maybe A → Maybe B
    mapᴹ = ⊎-map id

    -- If mapᴹ f x does not have a value, then x does not have a
    -- value.

    mapᴹ-↑ : ∀ {f : A → B} x → mapᴹ f x ↑ → x ↑
    mapᴹ-↑ nothing  _  = refl
    mapᴹ-↑ (just _) ()

    -- The function mapᴹ f preserves LE.

    mapᴹ-LE : ∀ {f : A → B} {x y} →
              LE x y → LE (mapᴹ f x) (mapᴹ f y)
    mapᴹ-LE =
      ⊎-map (cong (mapᴹ _)) (Σ-map (cong (mapᴹ _)) (_∘ mapᴹ-↑ _))

    -- The function mapᴹ f ∘_ preserves Increasing.

    mapᴹ-Increasing : ∀ {f : A → B} {g} →
                      Increasing g → Increasing (mapᴹ f ∘ g)
    mapᴹ-Increasing = mapᴹ-LE ∘_

-- A map function for Delay.

map : ∀ {a b} {A : Set a} {B : Set b} →
      (A → B) → Delay A → Delay B
map f = Σ-map (mapᴹ f ∘_) mapᴹ-Increasing

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

  -- If A is a set, then LE is a family of propositions.

  LE-propositional :
    Is-set A → {x y : Maybe A} → Is-proposition (LE x y)
  LE-propositional A-set = _⇔_.from propositional⇔irrelevant (irr _ _)
    where
    irr : ∀ x y → Proof-irrelevant (LE x y)
    irr nothing _ = _⇔_.to propositional⇔irrelevant $
                      mono₁ 0 LE-nothing-contractible

    irr (just x) (just y) (inj₁ p) (inj₁ q) = cong inj₁ $
      _⇔_.to set⇔UIP (Maybe-closure 0 A-set) p q

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
      (mono₁ (1 + n) (Maybe-closure n h _ _))
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
-- An unused lemma

private

  -- If the embedding g maps nothing to nothing and just to just, then
  -- there is an isomorphism between Increasing f and
  -- Increasing (g ∘ f).

  Increasing-∘ :
    ∀ {a b} {A : Set a} {B : Set b} {f : ℕ → Maybe A} →
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
      ; right-inverse-of = ext ∘ (to∘from ∘_)
      }
    ; left-inverse-of = ext ∘ (from∘to ∘_)
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
      _⇔_.to propositional⇔irrelevant
        (×-closure 1 (↑-propositional _) (¬-propositional ext))
        _ _

    from∘to : ∀ {n} (x : Increasing-at n f) → from (to x) ≡ x
    from∘to (inj₁ p) = cong inj₁ (
      g-injective (cong g′ p)  ≡⟨ _≃_.left-inverse-of (Embedding.equivalence g) _ ⟩∎
      p                        ∎)
    from∘to (inj₂ _) = cong inj₂ $
       _⇔_.to propositional⇔irrelevant
         (×-closure 1 (↑-propositional _) (¬-propositional ext))
         _ _

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
-- Theorems relating the two definitions of the delay monad to each
-- other and to another definition

private

  -- Building blocks used in the theorems below.

  module LE {a} {A : Set a} where

    -- The function to₁ is basically π from Section 7.1 of
    -- "Quotienting the Delay Monad by Weak Bisimilarity" by Chapman,
    -- Uustalu and Veltri, but the function proj₁ ∘ from is different
    -- from their function ε, which is defined so that (with the
    -- terminology used here) ε (now x) (suc n) = nothing.

    mutual

      to₁ : (ℕ → Maybe A) → D.Delay A ∞
      to₁ f = to′ (f 0)
        module To where
        to′ : Maybe A → D.Delay A ∞
        to′ (just x) = now x
        to′ nothing  =
          later (∞to₁ (f ∘ suc))

      ∞to₁ : (ℕ → Maybe A) → D.∞Delay A ∞
      force (∞to₁ x) = to₁ x

    to : Delay A → D.Delay A ∞
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

module _ {a} {A : Set a} where

  -- The two definitions are logically equivalent.

  Delay⇔Delay : Delay A ⇔ D.Delay A ∞
  Delay⇔Delay = record { to = LE.to; from = LE.from }

  -- There is a split surjection from D.Delay A ∞ to Delay A.

  Delay↠Delay : D.Delay A ∞ ↠ Delay A
  Delay↠Delay = record
    { logical-equivalence = inverse Delay⇔Delay
    ; right-inverse-of    = from∘to
    }
    where
    open LE

    from∘to : ∀ x → from (to x) ≡ x
    from∘to x = Σ-≡,≡→≡
      (ext (proj₁∘from∘to x))
      (ext λ n →

         subst Increasing
               (ext (proj₁∘from∘to x))
               (proj₂ (from (to x)))
               n                        ≡⟨ sym $ push-subst-application (ext (proj₁∘from∘to x)) (flip Increasing-at) ⟩

         subst (Increasing-at n)
               (ext (proj₁∘from∘to x))
               (proj₂ (from (to x)) n)  ≡⟨ uncurry proj₂∘from∘to x n _ refl ⟩∎

         proj₂ x n                      ∎)

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
              (ext (proj₁∘from∘to′ g g-increasing y g0≡y))
              (proj₂ (from (To.to′ g y)) n)
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
              (ext (proj₁∘from∘to′ g g-inc nothing g0↑))
              (proj₂ (from (to (g ∘ suc , g-inc ∘ suc))) n)              ≡⟨⟩

        subst (Increasing-at n ∘ (_∘ suc))
              (ext (proj₁∘from∘to′ g g-inc nothing g0↑))
              (proj₂ (from (to (g ∘ suc , g-inc ∘ suc))) n)              ≡⟨ subst-∘ (Increasing-at n) (_∘ suc)
                                                                                    (ext (proj₁∘from∘to′ g g-inc nothing g0↑)) ⟩
        subst (Increasing-at n)
              (cong (_∘ suc) (ext (proj₁∘from∘to′ g g-inc nothing g0↑)))
              (proj₂ (from (to (g ∘ suc , g-inc ∘ suc))) n)              ≡⟨ cong (λ eq → subst (Increasing-at n) eq
                                                                                               (proj₂ (from (to (g ∘ suc , g-inc ∘ suc))) n)) $
                                                                              cong-∘-ext (proj₁∘from∘to′ g g-inc nothing g0↑) ⟩
        subst (Increasing-at n)
              (ext (proj₁∘from∘to′ g g-inc nothing g0↑ ∘ suc))
              (proj₂ (from (to (g ∘ suc , g-inc ∘ suc))) n)              ≡⟨⟩

        subst (Increasing-at n)
              (ext (proj₁∘from∘to′ (g ∘ suc) (g-inc ∘ suc) _ refl))
              (proj₂ (from (to (g ∘ suc , g-inc ∘ suc))) n)              ≡⟨ proj₂∘from∘to (g ∘ suc) (g-inc ∘ suc) n _ refl ⟩∎

        g-inc (suc n)                                                    ∎

  -- The two definitions are isomorphic (assuming extensionality).

  Delay↔Delay : Strong-bisimilarity.Extensionality a →
                Delay A ↔ D.Delay A ∞
  Delay↔Delay delay-ext = record
    { surjection = record
      { logical-equivalence = Delay⇔Delay
      ; right-inverse-of    = delay-ext ∘ to∘from
      }
    ; left-inverse-of = _↠_.right-inverse-of Delay↠Delay
    }
    where
    open LE

    mutual

      to∘from : ∀ x → to (from x) ∼ x
      to∘from (now x)   = now-cong
      to∘from (later x) = later-cong (∞to∘from (force x))

      ∞to∘from : ∀ x → to (from x) ∞∼ x
      force (∞to∘from x) = to∘from x

  -- There is a split surjection from ℕ → Maybe A (without any
  -- requirement that the sequences are increasing) to D.Delay A ∞
  -- (assuming extensionality).
  --
  -- Chapman, Uustalu and Veltri prove this result in "Quotienting the
  -- Delay Monad by Weak Bisimilarity".

  →↠Delay-coinductive : Strong-bisimilarity.Extensionality a →
                        (ℕ → Maybe A) ↠ D.Delay A ∞
  →↠Delay-coinductive delay-ext = record
    { logical-equivalence = record
      { to   = LE.to₁
      ; from = proj₁ ∘ LE.from
      }
    ; right-inverse-of = _↔_.right-inverse-of (Delay↔Delay delay-ext)
    }

  -- There is also a split surjection from ℕ → Maybe A to Delay A.

  →↠Delay-function : (ℕ → Maybe A) ↠ Delay A
  →↠Delay-function = record
    { logical-equivalence = record
      { to   = LE.from ∘ LE.to₁
      ; from = proj₁
      }
    ; right-inverse-of = _↠_.right-inverse-of Delay↠Delay
    }

------------------------------------------------------------------------
-- Two eliminators for Delay (A / R)

-- The constructions used in this section are based on (but perhaps
-- not quite identical to) those underlying Theorem 1 in "Quotienting
-- the Delay Monad by Weak Bisimilarity" by Chapman, Uustalu and
-- Veltri.

-- There is a function from (ℕ → Maybe A) / (ℕ →ᴾ Maybeᴾ R) to
-- Delay (A / R).

→Maybe/→ :
  ∀ {a r} {A : Set a} {R : A → A → Proposition r} →
  (ℕ → Maybe A) / (ℕ →ᴾ Maybeᴾ R) → Delay (A / R)
→Maybe/→ f =
  _↠_.to →↠Delay-function (_↔_.to Maybe/-comm ∘ ℕ→/-comm-to f)

-- The definitions below make use of some assumptions: propositional
-- extensionality and countable choice, and a propositional
-- equivalence relation R.

module _
  {a r} {A : Set a} {R : A → A → Proposition r}
  (prop-ext : Propositional-extensionality r)
  (cc : Axiom-of-countable-choice (a ⊔ r))
  (R-equiv : Is-equivalence-relation R)
  where

  private

    -- An abbreviation.

    ℕ→/-comm′ =
      ℕ→/-comm prop-ext cc
        (Maybeᴾ-preserves-Is-equivalence-relation {R = R} R-equiv)

  -- →Maybe/→ has a right inverse.

  →Maybe/↠ :
    (ℕ → Maybe A) / (ℕ →ᴾ Maybeᴾ R) ↠ Delay (A / R)
  →Maybe/↠ =
    (ℕ → Maybe A) / (ℕ →ᴾ Maybeᴾ R)  ↔⟨ ℕ→/-comm′ ⟩
    (ℕ → Maybe A / Maybeᴾ R)         ↔⟨ Eq.∀-preserves ext (λ _ → Eq.↔⇒≃ Maybe/-comm) ⟩
    (ℕ → Maybe (A / R))              ↝⟨ →↠Delay-function ⟩□
    Delay (A / R)                    □

  private

    to-→Maybe/↠ : _↠_.to →Maybe/↠ ≡ →Maybe/→
    to-→Maybe/↠ = refl

  -- On part of the domain of →Maybe/→ the right inverse is also a
  -- left inverse.

  →Maybe/↠-partial-left-inverse :
    (x : Delay A) →
    _↠_.from →Maybe/↠ (→Maybe/→ [ proj₁ x ]) ≡ [ proj₁ x ]
  →Maybe/↠-partial-left-inverse (f , inc) =
    _↠_.from →Maybe/↠ (→Maybe/→ [ f ])                                ≡⟨⟩

    _↔_.from ℕ→/-comm′ (λ n →
      _↔_.from Maybe/-comm $
      _↠_.from →↠Delay-function
        (_↠_.to →↠Delay-function (_↔_.to Maybe/-comm ∘ [_] ∘ f))
        n)                                                            ≡⟨ cong (λ g → _↔_.from ℕ→/-comm′ λ n →
                                                                                       _↔_.from Maybe/-comm (_↠_.from →↠Delay-function
                                                                                                               (_↠_.to →↠Delay-function (g ∘ f))
                                                                                                               n)) $
                                                                           Maybe/-comm-[] ⟩
    _↔_.from ℕ→/-comm′ (λ n →
      _↔_.from Maybe/-comm $
      _↠_.from →↠Delay-function
        (_↠_.to →↠Delay-function (mapᴹ [_] ∘ f))
        n)                                                            ≡⟨⟩

    _↔_.from ℕ→/-comm′ (λ n →
      _↔_.from Maybe/-comm $
      _↠_.from →↠Delay-function
        (_↠_.to →↠Delay-function
           (_↠_.from →↠Delay-function (map [_] (f , inc))))
        n)                                                            ≡⟨ cong (λ x → _↔_.from ℕ→/-comm′ λ n →
                                                                                       _↔_.from Maybe/-comm (_↠_.from →↠Delay-function x n)) $
                                                                           _↠_.right-inverse-of →↠Delay-function (map [_] (f , inc)) ⟩
    _↔_.from ℕ→/-comm′ (λ n →
      _↔_.from Maybe/-comm $
      _↠_.from →↠Delay-function (map [_] (f , inc)) n)                ≡⟨⟩

    _↔_.from ℕ→/-comm′ (λ n → _↔_.from Maybe/-comm $ mapᴹ [_] (f n))  ≡⟨ cong (λ g → _↔_.from ℕ→/-comm′ λ n → _↔_.from Maybe/-comm (g (f n))) $
                                                                           sym Maybe/-comm-[] ⟩
    _↔_.from ℕ→/-comm′ (λ n →
      _↔_.from Maybe/-comm (_↔_.to Maybe/-comm [ f n ]))              ≡⟨ cong (_↔_.from ℕ→/-comm′) (ext λ n →
                                                                           _↔_.left-inverse-of Maybe/-comm [ f n ]) ⟩
    _↔_.from ℕ→/-comm′ (λ n → [ f n ])                                ≡⟨⟩

    _↔_.from ℕ→/-comm′ (ℕ→/-comm-to [ f ])                            ≡⟨ _↔_.left-inverse-of ℕ→/-comm′ [ f ] ⟩∎

    [ f ]                                                             ∎

  private

    -- Dummy is a local module used to ensure that the definitions
    -- inside it get their own abstract block.

    module Dummy where

      abstract

        -- A quotient-like eliminator for Delay (A / R).

        Delay/-elim₁ :
          ∀ {p} (P : Delay (A / R) → Set p)
          (p-[] : (f : ℕ → Maybe A) → P (→Maybe/→ [ f ])) →
          (∀ {f g} (r : proj₁ ((ℕ →ᴾ Maybeᴾ R) f g)) →
           subst P (cong →Maybe/→
                         ([]-respects-relation {x = f} {y = g} r))
                   (p-[] f) ≡
           p-[] g) →
          (∀ x → Is-set (P x)) →
          ∀ x → P x
        Delay/-elim₁ = ↠-eliminator →Maybe/↠

        -- Simplification lemma for Delay/-elim₁.

        Delay/-elim₁-[] :
          ∀ {p} (P : Delay (A / R) → Set p)
          (p-[] : (f : ℕ → Maybe A) → P (→Maybe/→ [ f ]))
          (ok :
             ∀ {f g} (r : proj₁ ((ℕ →ᴾ Maybeᴾ R) f g)) →
             subst P (cong →Maybe/→
                           ([]-respects-relation {x = f} {y = g} r))
                     (p-[] f) ≡
             p-[] g)
          (P-set : ∀ x → Is-set (P x)) (x : Delay A) →
          Delay/-elim₁ P p-[] ok P-set (→Maybe/→ [ proj₁ x ]) ≡
          p-[] (proj₁ x)
        Delay/-elim₁-[] P p-[] ok P-set x =
          ↠-eliminator-[] →Maybe/↠ P p-[] ok P-set
            (_↠_.from →↠Delay-function x)
            (→Maybe/↠-partial-left-inverse x)

  open Dummy public

module _
  {a r} {A : Set a} {R : A → A → Proposition r}
  where

  -- The function map ([_] {R = R}) respects Delayᴾ R.

  map-[]-cong :
    ∀ x y → proj₁ (Delayᴾ R x y) → map ([_] {R = R}) x ≡ map [_] y
  map-[]-cong x y r =
    _↔_.to (equality-characterisation /-is-set)
      (ext λ n → lemma (proj₁ x n) (proj₁ y n) (r n))
    where
    lemma : ∀ x y → proj₁ (Maybeᴾ R x y) →
            mapᴹ [_] x ≡ mapᴹ [_] y
    lemma nothing  nothing  = const refl
    lemma (just x) (just y) = cong inj₂ ∘ []-respects-relation
    lemma nothing  (just y) ()
    lemma (just x) nothing  ()

  -- The function
  -- _↠_.from →↠Delay-function ∘ _↠_.to →↠Delay-function respects
  -- ℕ →ᴾ Maybeᴾ R.

  from-to-→↠Delay-function-cong :
    let open _↠_ →↠Delay-function in
    (f g : ℕ → Maybe A) →
    proj₁ ((ℕ →ᴾ Maybeᴾ R) f g) →
    proj₁ ((ℕ →ᴾ Maybeᴾ R) (from (to f)) (from (to g)))
  from-to-→↠Delay-function-cong f g r =
    helper f g r (f 0) (g 0) (r 0)
    where
    helper :
      ∀ f g → proj₁ ((ℕ →ᴾ Maybeᴾ R) f g) →
      ∀ x y → proj₁ (Maybeᴾ R x y) →
      proj₁ ((ℕ →ᴾ Maybeᴾ R) (proj₁ (LE.from (LE.To.to′ f x)))
                             (proj₁ (LE.from (LE.To.to′ g y))))
    helper f g rs (just x) (just y) r n       = r
    helper f g rs nothing  nothing  r zero    = r
    helper f g rs nothing  nothing  r (suc n) =
      helper (f ∘ suc) (g ∘ suc) (rs ∘ suc) (f 1) (g 1) (rs 1) n

    helper _ _ _ (just _) nothing  ()
    helper _ _ _ nothing  (just _) ()

  -- A simplification lemma for →Maybe/→.

  →Maybe/→-[] :
    (f : ℕ → Maybe A) →
    →Maybe/→ [ f ] ≡
    map ([_] {R = R}) (_↠_.to →↠Delay-function f)
  →Maybe/→-[] f = _↔_.to (equality-characterisation /-is-set)
    (proj₁ (→Maybe/→ [ f ])                                          ≡⟨⟩
     proj₁ (_↠_.to →↠Delay-function (_↔_.to Maybe/-comm ∘ [_] ∘ f))  ≡⟨ cong (λ g → proj₁ (_↠_.to →↠Delay-function (g ∘ f))) $ Maybe/-comm-[] ⟩
     proj₁ (_↠_.to →↠Delay-function (mapᴹ [_] ∘ f))                  ≡⟨ ext (helper f (f 0)) ⟩
     mapᴹ [_] ∘ proj₁ (_↠_.to →↠Delay-function f)                    ≡⟨⟩
     proj₁ (map [_] (_↠_.to →↠Delay-function f))                     ∎)
    where
    helper :
       ∀ f x n →
       proj₁ (LE.from (LE.To.to′ (mapᴹ [_] ∘ f) (mapᴹ [_] x))) n ≡
       mapᴹ [_] (proj₁ (LE.from (LE.To.to′ f x)) n)
    helper f (just x) n       = refl
    helper f nothing  zero    = refl
    helper f nothing  (suc n) = helper (f ∘ suc) (f 1) n

-- The definitions below make use of some assumptions: propositional
-- extensionality and countable choice, and a propositional
-- equivalence relation R.

module _
  {a p r} {A : Set a} {R : A → A → Proposition r}
  (prop-ext : Propositional-extensionality r)
  (cc : Axiom-of-countable-choice (a ⊔ r))
  (R-equiv : Is-equivalence-relation R)
  where

  abstract

    -- A second quotient-like eliminator for Delay (A / R).
    --
    -- This eliminator corresponds to Theorem 1 in "Quotienting the
    -- Delay Monad by Weak Bisimilarity" by Chapman, Uustalu and
    -- Veltri.

    Delay/-elim₂ :
      (P : Delay (A / R) → Set p)
      (p-[] : (x : Delay A) → P (map [_] x)) →
      (∀ {x y} (r : proj₁ (Delayᴾ R x y)) →
       subst P (map-[]-cong x y r) (p-[] x) ≡ p-[] y) →
      (∀ x → Is-set (P x)) →
      ∀ x → P x
    Delay/-elim₂ P p-[] ok P-set =
      Delay/-elim₁ prop-ext cc R-equiv P
      (λ f → subst P (lemma₁ f) (p-[] (_↠_.to →↠Delay-function f)))
      lemma₂ P-set
      where
      lemma₁ = sym ∘ →Maybe/→-[]

      lemma₂ :
        ∀ {f g} r →
        subst P
          (cong →Maybe/→ ([]-respects-relation {x = f} {y = g} r))
          (subst P (lemma₁ f) (p-[] (_↠_.to →↠Delay-function f))) ≡
        subst P (lemma₁ g) (p-[] (_↠_.to →↠Delay-function g))
      lemma₂ {f} {g} r =
        let p  = p-[] (_↠_.to →↠Delay-function f)
            r′ = cong →Maybe/→ ([]-respects-relation {x = f} {y = g} r)
            r″ = trans (trans (lemma₁ f) r′) (sym (lemma₁ g))
        in
        subst P r′ (subst P (lemma₁ f) p)                               ≡⟨ subst-subst P (lemma₁ f) r′ p ⟩

        subst P (trans (lemma₁ f) r′) p                                 ≡⟨ cong (λ eq → subst P eq p) $
                                                                             sym $ trans-[trans-sym]- _ (lemma₁ g) ⟩
        subst P (trans r″ (lemma₁ g)) p                                 ≡⟨ sym $ subst-subst P
                                                                                   (trans (trans (lemma₁ f) r′) (sym (lemma₁ g)))
                                                                                   (lemma₁ g)
                                                                                   p ⟩
        subst P (lemma₁ g) (subst P r″ p)                               ≡⟨ cong (λ eq → subst P (lemma₁ g) (subst P eq p)) $
                                                                             _⇔_.to propositional⇔irrelevant
                                                                               (Delay-closure 0 /-is-set _ _)
                                                                               r″
                                                                               (map-[]-cong (_↠_.to →↠Delay-function f)
                                                                                            (_↠_.to →↠Delay-function g)
                                                                                            (from-to-→↠Delay-function-cong f g r)) ⟩
        subst P (lemma₁ g)
          (subst P (map-[]-cong (_↠_.to →↠Delay-function f)
                                (_↠_.to →↠Delay-function g)
                                (from-to-→↠Delay-function-cong f g r))
                   p)                                                   ≡⟨ cong (subst P (lemma₁ g)) (ok _) ⟩∎

        subst P (lemma₁ g) (p-[] (_↠_.to →↠Delay-function g))           ∎

    -- Simplification lemma for Delay/-elim₂.

    Delay/-elim₂-[] :
      (P : Delay (A / R) → Set p)
      (p-[] : (x : Delay A) → P (map [_] x))
      (ok : ∀ {x y} (r : proj₁ (Delayᴾ R x y)) →
            subst P (map-[]-cong x y r) (p-[] x) ≡ p-[] y)
      (P-set : ∀ x → Is-set (P x)) →
      ∀ x → Delay/-elim₂ P p-[] ok P-set (map [_] x) ≡ p-[] x
    Delay/-elim₂-[] P p-[] ok P-set x =
      Delay/-elim₁ prop-ext cc R-equiv P
        (λ f → subst P (lemma₁ f) (p-[] (_↠_.to →↠Delay-function f)))
        _ P-set (map [_] x)                                                ≡⟨ sym $ dependent-cong
                                                                                      (Delay/-elim₁ prop-ext cc R-equiv P
                                                                                                    (λ f → subst P (lemma₁ f)
                                                                                                             (p-[] (_↠_.to →↠Delay-function f)))
                                                                                                    _ P-set)
                                                                                      lemma₂ ⟩
      subst P lemma₂
        (Delay/-elim₁ prop-ext cc R-equiv P
           (λ f → subst P (lemma₁ f) (p-[] (_↠_.to →↠Delay-function f)))
           _ P-set (→Maybe/→ [ proj₁ x ]))                                 ≡⟨⟩

      subst P lemma₂
        (Delay/-elim₁ prop-ext cc R-equiv P
           (λ f → subst P (lemma₁ f) (p-[] (_↠_.to →↠Delay-function f)))
           _ P-set (→Maybe/→ [ proj₁ x ]))                                 ≡⟨ cong (subst P lemma₂) $
                                                                                Delay/-elim₁-[] prop-ext cc R-equiv _ _ _ _ x ⟩
      subst P lemma₂
        (subst P (lemma₁ (proj₁ x))
           (p-[] (_↠_.to →↠Delay-function (proj₁ x))))                     ≡⟨ subst-subst P (lemma₁ (proj₁ x)) lemma₂ _ ⟩

      subst P (trans (lemma₁ (proj₁ x)) lemma₂)
        (p-[] (_↠_.to →↠Delay-function (proj₁ x)))                         ≡⟨ cong (λ p → subst P p (p-[] (_↠_.to →↠Delay-function (proj₁ x)))) $
                                                                                trans--[trans-sym]
                                                                                  (lemma₁ (proj₁ x))
                                                                                  (cong (map [_]) $ _↠_.right-inverse-of →↠Delay-function x) ⟩
      subst P (cong (map [_]) $ _↠_.right-inverse-of →↠Delay-function x)
        (p-[] (_↠_.to →↠Delay-function (proj₁ x)))                         ≡⟨ sym $ subst-∘ P (map [_]) (_↠_.right-inverse-of →↠Delay-function x) ⟩

      subst (P ∘ map [_]) (_↠_.right-inverse-of →↠Delay-function x)
        (p-[] (_↠_.to →↠Delay-function (proj₁ x)))                         ≡⟨ dependent-cong p-[] (_↠_.right-inverse-of →↠Delay-function x) ⟩∎

      p-[] x                                                               ∎
      where
      lemma₁ = sym ∘ →Maybe/→-[]

      lemma₂ =
        →Maybe/→ [ proj₁ x ]                         ≡⟨ sym $ lemma₁ (proj₁ x) ⟩
        map [_] (_↠_.to →↠Delay-function (proj₁ x))  ≡⟨ cong (map [_]) $ _↠_.right-inverse-of →↠Delay-function x ⟩∎
        map [_] x                                    ∎

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

  ⇓⇔⇓ : ∀ x {y} → x ⇓ y ⇔ _⇔_.to Delay⇔Delay x W.⇓ y
  ⇓⇔⇓ x = record
    { to   = λ { (n , fn↓y) → to n _ (proj₂ x) refl fn↓y }
    ; from = from _ refl
    }
    where
    to : ∀ {f : ℕ → Maybe A} n x {y} →
         Increasing f →
         x ≡ f 0 → f n ↓ y → LE.To.to′ f x W.⇓ y
    to (suc n) nothing f-inc f0↑ fn↓y =
      W.laterʳ (to n _ (f-inc ∘ suc) refl fn↓y)

    to {f} zero nothing {y} _ f0↑ fn↓y =
      ⊥-elim $ ⊎.inj₁≢inj₂ (
        nothing  ≡⟨ f0↑ ⟩
        f 0      ≡⟨ fn↓y ⟩∎
        just y   ∎)

    to {f} n (just x) {y} f-inc f0↓x fn↓y =
      subst (_ W.⇓_)
            (⊎.cancel-inj₂ {A = ⊤}
               (just x  ≡⟨ sym $ ↓-upwards-closed₀ f-inc (sym f0↓x) n ⟩
                f n     ≡⟨ fn↓y ⟩∎
                just y  ∎))
            W.now-cong

    from : ∀ {f : ℕ → Maybe A} {y} x →
           x ≡ f 0 → LE.To.to′ f x W.⇓ y → ∃ λ n → f n ↓ y
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

  ⊑⇔⊑ : ∀ x y →
        x ⊑ y ⇔ _⇔_.to Delay⇔Delay x PO.⊑ _⇔_.to Delay⇔Delay y
  ⊑⇔⊑ x y =
    x ⊑ y                                                              ↝⟨ F.id ⟩
    (∀ z → x ⇓ z → y ⇓ z)                                              ↝⟨ ∀-cong-⇔ (λ _ → →-cong-⇔ (⇓⇔⇓ x) (⇓⇔⇓ y)) ⟩
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

  -- The ordering relation _∥⊑∥_ is reflexive.

  ∥⊑∥-reflexive : ∀ x → x ∥⊑∥ x
  ∥⊑∥-reflexive _ = λ _ → id

  -- The ordering relation _∥⊑∥_ is transitive.

  ∥⊑∥-transitive : ∀ x y z → x ∥⊑∥ y → y ∥⊑∥ z → x ∥⊑∥ z
  ∥⊑∥-transitive _ _ _ p q = λ z → q z ∘ p z

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

  -- Weak bisimilarity is an equivalence relation.

  ≈-is-equivalence-relation : Quotient′.Is-equivalence-relation _≈_
  ≈-is-equivalence-relation = record
    { reflexive  = λ {x} → ∥⊑∥-reflexive x , ∥⊑∥-reflexive x
    ; symmetric  = λ { (p , q) → q , p }
    ; transitive = λ {x y z} → Σ-zip (∥⊑∥-transitive x y z)
                                     (flip (∥⊑∥-transitive z y x))
    }

  -- The notion of weak bisimilarity defined here is logically
  -- equivalent (via Delay⇔Delay) to the one defined for the
  -- coinductive delay monad (if A is a set).

  ≈⇔≈ :
    Is-set A →
    ∀ x y → x ≈ y ⇔ _⇔_.to Delay⇔Delay x W.≈ _⇔_.to Delay⇔Delay y
  ≈⇔≈ A-set x y =
    x ∥⊑∥ y × y ∥⊑∥ x                ↝⟨ inverse (⊑⇔∥⊑∥ A-set x y ×-cong ⊑⇔∥⊑∥ A-set y x) ⟩
    x ⊑ y × y ⊑ x                    ↝⟨ ⊑⇔⊑ x y ×-cong ⊑⇔⊑ y x ⟩
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
