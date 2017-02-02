------------------------------------------------------------------------
-- Two eliminators for Delay-monad.Alternative.Delay (A / R)
------------------------------------------------------------------------

-- This module is largely based on (but perhaps not quite identical
-- to) the development underlying Theorem 1 in "Quotienting the Delay
-- Monad by Weak Bisimilarity" by Chapman, Uustalu and Veltri.

{-# OPTIONS --without-K --rewriting #-}

module Delay-monad.Alternative.Eliminators where

open import Equality.Propositional
open import H-level.Truncation.Propositional
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (↑)
open import Quotient.HIT

open import Bijection equality-with-J using (_↔_)
import Equivalence equality-with-J as Eq
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

open import Delay-monad.Alternative
open import Delay-monad.Alternative.Equivalence
open import Delay-monad.Alternative.Properties

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
-- The first eliminator

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

------------------------------------------------------------------------
-- The second eliminator

-- Pointwise lifting of binary relations to the delay monad.

Delayᴾ :
  ∀ {a r} {A : Set a} →
  (A → A → Proposition r) →
  Delay A → Delay A → Proposition r
Delayᴾ R = (ℕ →ᴾ Maybeᴾ R) on proj₁

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
      proj₁ ((ℕ →ᴾ Maybeᴾ R)
               (proj₁ (Delay⇔Delay.from (Delay⇔Delay.To.to′ f x)))
               (proj₁ (Delay⇔Delay.from (Delay⇔Delay.To.to′ g y))))
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
       proj₁ (Delay⇔Delay.from
                (Delay⇔Delay.To.to′ (mapᴹ [_] ∘ f) (mapᴹ [_] x))) n ≡
       mapᴹ [_] (proj₁ (Delay⇔Delay.from (Delay⇔Delay.To.to′ f x)) n)
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
