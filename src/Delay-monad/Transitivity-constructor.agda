------------------------------------------------------------------------
-- An example showing that transitivity-like proofs that are not
-- size-preserving can sometimes be used in a compositional way
------------------------------------------------------------------------

-- One can use the technique from "Beating the Productivity Checker
-- Using Embedded Languages" to make it possible to use
-- transitivity-like proofs that are not size-preserving in
-- corecursive definitions. However, it is unclear if this is ever
-- useful: the example presented below is rather contrived.

{-# OPTIONS --without-K #-}

module Delay-monad.Transitivity-constructor {a} {A : Set a} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Function-universe equality-with-J hiding (Kind)

open import Delay-monad
open import Delay-monad.Strong-bisimilarity as S
open import Delay-monad.Weak-bisimilarity

------------------------------------------------------------------------
-- Proof programs

-- There are two kinds of proof "programs", corresponding to strong
-- and weak bisimilarity.

data Kind : Set where
  strong weak : Kind

mutual

  -- Proof "programs".

  data Prog (i : Size) : Kind → Delay A ∞ → Delay A ∞ → Set a where

    -- Congruences.

    now-cong   : ∀ {k x} → Prog i k (now x) (now x)
    later-cong : ∀ {k x y} →
                 ∞Prog i k (force x) (force y) →
                 Prog i k (later x) (later y)

    -- Weak bisimilarity.

    laterʳ : ∀ {x y} → Prog i weak x (force y) → Prog i weak x (later y)
    laterˡ : ∀ {x y} → Prog i weak (force x) y → Prog i weak (later x) y

    -- Equational reasoning.
    --
    -- Note that if A is inhabited, then there is no size-preserving
    -- transitivity-like proof taking strong bisimilarity and weak
    -- bisimilarity to weak bisimilarity (see
    -- Delay-monad.Weak-bisimilarity.size-preserving-transitivity-∼≈ˡ⇔uninhabited).

    reflP  : ∀ {k} x → Prog i k x x
    symP   : ∀ {k x y} → Prog i k x y → Prog i k y x
    transP : ∀ {k x y z} →
             Prog i strong x y → Prog i k y z → Prog i k x z

  record ∞Prog (i : Size) (k : Kind) (x y : Delay A ∞) : Set a where
    coinductive
    field
      force : {j : Size< i} → Prog j k x y

open ∞Prog public

------------------------------------------------------------------------
-- Completeness

-- Proof programs are complete with respect to strong and weak
-- bisimilarity. Note that these proofs are size-preserving.

complete-strong : ∀ {i x y} →
                  Strongly-bisimilar i x y → Prog i strong x y
complete-strong now-cong       = now-cong
complete-strong (later-cong p) =
  later-cong λ { .force → complete-strong (force p) }

complete-weak : ∀ {i x y} → Weakly-bisimilar i x y → Prog i weak x y
complete-weak now-cong       = now-cong
complete-weak (laterʳ p)     = laterʳ (complete-weak p)
complete-weak (laterˡ p)     = laterˡ (complete-weak p)
complete-weak (later-cong p) =
  later-cong λ { .force → complete-weak (force p) }

------------------------------------------------------------------------
-- Soundness

-- Proof WHNFs.

data WHNF (i : Size) : Kind → Delay A ∞ → Delay A ∞ → Set a where
  now-cong   : ∀ {k x} → WHNF i k (now x) (now x)
  later-cong : ∀ {k x y} →
               ∞Prog i k (force x) (force y) →
               WHNF i k (later x) (later y)
  laterʳ     : ∀ {x y} →
               WHNF i weak x (force y) → WHNF i weak x (later y)
  laterˡ     : ∀ {x y} →
               WHNF i weak (force x) y → WHNF i weak (later x) y

-- Reflexivity.

reflW : ∀ {i k} x → WHNF i k x x
reflW (now   x) = now-cong
reflW (later x) = later-cong λ { .force → reflP (force x) }

-- Symmetry.

symW : ∀ {i k x y} → WHNF i k x y → WHNF i k y x
symW now-cong       = now-cong
symW (later-cong p) = later-cong λ { .force → symP (force p) }
symW (laterʳ p)     = laterˡ (symW p)
symW (laterˡ p)     = laterʳ (symW p)

-- Transitivity for strong WHNFs.

trans∼∼W : ∀ {i x y z} →
           WHNF i strong x y → WHNF i strong y z → WHNF i strong x z
trans∼∼W now-cong       q              = q
trans∼∼W (later-cong p) (later-cong q) =
  later-cong λ { .force → transP (force p) (force q) }

-- Strong equality programs can be turned into WHNFs.

whnf∼ : ∀ {i x y} → Prog i strong x y → WHNF i strong x y
whnf∼ now-cong       = now-cong
whnf∼ (later-cong p) = later-cong p
whnf∼ (reflP x)      = reflW x
whnf∼ (symP p)       = symW (whnf∼ p)
whnf∼ (transP p q)   = trans∼∼W (whnf∼ p) (whnf∼ q)

-- Strong proof programs are sound with respect to strong
-- bisimilarity. Note that these proofs are size-preserving.

mutual

  sound-strong : ∀ {i x y} →
                 Prog i strong x y → Strongly-bisimilar i x y
  sound-strong p = soundW-strong (whnf∼ p)

  soundW-strong : ∀ {i x y} →
                  WHNF i strong x y → Strongly-bisimilar i x y
  soundW-strong now-cong       = now-cong
  soundW-strong (later-cong p) =
    later-cong λ { .force → sound-strong (force p) }

-- Another transitivity lemma. This lemma cannot, in general, be made
-- fully size-preserving (see not-fully-size-preserving below).

trans∼-W : ∀ {i k x y z} →
           WHNF ∞ strong x y → WHNF i k y z → WHNF i k x z
trans∼-W now-cong       q              = q
trans∼-W p              (laterʳ q)     = laterʳ (trans∼-W p q)
trans∼-W (later-cong p) (laterˡ q)     = laterˡ (trans∼-W (whnf∼ (force p)) q)
trans∼-W (later-cong p) (later-cong q) =
  later-cong λ { .force → transP (force p) (force q) }

-- All fully defined programs can be turned into WHNFs.

whnf : ∀ {i k x y} → Prog ∞ k x y → WHNF i k x y
whnf now-cong       = now-cong
whnf (later-cong p) = later-cong p
whnf (laterʳ p)     = laterʳ (whnf p)
whnf (laterˡ p)     = laterˡ (whnf p)
whnf (reflP x)      = reflW x
whnf (symP p)       = symW (whnf p)
whnf (transP p q)   = trans∼-W (whnf p) (whnf q)

-- Weak proof programs are sound with respect to weak bisimilarity.
-- Note that these proofs are /not/ guaranteed to be size-preserving.

mutual

  sound-weak : ∀ {i x y} → Prog ∞ weak x y → Weakly-bisimilar i x y
  sound-weak p = soundW-weak (whnf p)

  soundW-weak : ∀ {i x y} → WHNF ∞ weak x y → Weakly-bisimilar i x y
  soundW-weak now-cong       = now-cong
  soundW-weak (laterʳ p)     = laterʳ  (soundW-weak p)
  soundW-weak (laterˡ p)     = laterˡ  (soundW-weak p)
  soundW-weak (later-cong p) =
    later-cong λ { .force → sound-weak (force p) }

------------------------------------------------------------------------
-- Some negative results

-- The soundness proof for weak proof programs can be made
-- size-preserving iff A is uninhabited.

size-preserving⇔uninhabited :
  (∀ {i x y} → Prog i weak x y → Weakly-bisimilar i x y) ⇔ ¬ A
size-preserving⇔uninhabited = record
  { to   = (∀ {i x y} → Prog i weak x y → Weakly-bisimilar i x y)  ↝⟨ (λ sound p q → sound (transP (complete-strong p) (complete-weak q))) ⟩
           Transitivity-∼≈ˡ                                        ↝⟨ _⇔_.to size-preserving-transitivity-∼≈ˡ⇔uninhabited ⟩□
           ¬ A                                                     □
  ; from = ¬ A                                                     ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≈ y)                                         ↝⟨ (λ trivial {_ _ _} _ → trivial _ _) ⟩□
           (∀ {i x y} → Prog i weak x y → Weakly-bisimilar i x y)  □
  }

-- The lemma trans∼-W cannot be made fully size-preserving (assuming
-- that A is inhabited).

not-fully-size-preserving :
  (∀ {i k x y z} →
   WHNF i strong x y → WHNF i k y z → WHNF i k x z) →
  ¬ A
not-fully-size-preserving trans x = contradiction ∞
  where

  never≉now : ∀ {i} → ¬ WHNF i weak never (now x)
  never≉now (laterˡ p) = never≉now p

  mutual

    never≈now : ∀ {i} → WHNF i weak never (now x)
    never≈now =
      trans (later-cong {y = record { force = now x }} ∞never∼now)
            (laterˡ now-cong)

    ∞never∼now : ∀ {i} → ∞Prog i strong never (now x)
    force ∞never∼now {j = j} = ⊥-elim (contradiction j)

    contradiction : Size → ⊥
    contradiction i = never≉now (never≈now {i = i})

-- One might wonder why the counterexample above cannot be adapted so
-- that it also applies to programs, for which a size-preserving
-- transitivity constructor exists. The following lemma documents one
-- attempt at adapting the counterexample. Note that the new
-- counterexample is based on the assumption that one can convert a
-- strong bisimilarity program /of any size/ relating never and x to a
-- proof that x is /equal/ to never.

partially-adapted-counterexample :
  (∀ {i x} → Prog i strong never x → x ≡ never) →
  ¬ A
partially-adapted-counterexample convert x = contradiction ∞
  where
  mutual

    now∼→≡now : ∀ {i x y} → Prog i strong (now x) y → y ≡ now x
    now∼→≡now now-cong     = refl
    now∼→≡now (reflP _)    = refl
    now∼→≡now (symP p)     = ∼now→≡now p
    now∼→≡now (transP p q) rewrite now∼→≡now p = now∼→≡now q

    ∼now→≡now : ∀ {i x y} → Prog i strong x (now y) → x ≡ now y
    ∼now→≡now now-cong     = refl
    ∼now→≡now (reflP _)    = refl
    ∼now→≡now (symP p)     = now∼→≡now p
    ∼now→≡now (transP p q) rewrite ∼now→≡now q = ∼now→≡now p

  mutual

    now≉Pnever : ∀ {i} → ¬ Prog i weak (now x) never
    now≉Pnever (laterʳ p)   = now≉Pnever p
    now≉Pnever (symP p)     = never≉Pnow p
    now≉Pnever (transP p q) rewrite now∼→≡now p = now≉Pnever q

    never≉Pnow : ∀ {i} → ¬ Prog i weak never (now x)
    never≉Pnow (laterˡ p)   = never≉Pnow p
    never≉Pnow (symP p)     = now≉Pnever p
    never≉Pnow (transP p q) rewrite convert p = never≉Pnow q

  mutual

    never≈Pnow : ∀ {i} → Prog i weak never (now x)
    never≈Pnow =
      transP (later-cong {y = record { force = now x }} ∞never∼Pnow)
             (laterˡ now-cong)

    ∞never∼Pnow : ∀ {i} → ∞Prog i strong never (now x)
    force ∞never∼Pnow {j = j} = ⊥-elim (contradiction j)

    contradiction : Size → ⊥
    contradiction i = never≉Pnow (never≈Pnow {i = i})

------------------------------------------------------------------------
-- A contrived example

-- Note the use of a strong bisimilarity program of size i as the
-- first argument to transitivity in the following example; this is
-- not supported by transitive-∼≈, which requires the first argument
-- to have size ∞.

exampleP : ∀ {i} → Prog i weak never never
exampleP {i} =
  transP (reflP {i = i} never) (later-cong λ { .force → exampleP })

example : ∀ {i} → Weakly-bisimilar i never never
example = sound-weak exampleP

-- However, note that the first argument could just as well have been
-- given the size ∞, in which case transitive-∼≈ works:

counterargument : ∀ {i} → Weakly-bisimilar i never (never {A = A})
counterargument =
  transitive-∼≈ (S.reflexive never)
                (later-cong λ { .force → counterargument })

-- Are there any applications in which strong and weak bisimilarities
-- are proved simultaneously? One can observe that, if the first
-- argument is never, then weak bisimilarity is contained in strong
-- (in a size-preserving way):

≈→∼ : ∀ {i} {x : Delay A ∞} →
      Weakly-bisimilar i never x → Strongly-bisimilar i never x
≈→∼ (later-cong p) = later-cong λ { .force → ≈→∼ (force p) }
≈→∼ (laterˡ p)     = ≈→∼ p
≈→∼ (laterʳ p)     = later-cong λ { .force → ≈→∼ p }

-- Perhaps one can find some compelling application of the technique
-- presented above if it can be combined with a lemma like ≈→∼.
-- However, it is unclear if such a combination is possible: the
-- soundness proof above relies on the fact that strong bisimilarity
-- programs contain no weak bisimilarity programs (in particular, no
-- transitivity proofs with a weak bisimilarity as the second
-- argument).
