------------------------------------------------------------------------
-- The expansion relation
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Delay-monad.Expansion {a} {A : Set a} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Function-universe equality-with-J hiding (_∘_)
open import H-level equality-with-J

open import Delay-monad
open import Delay-monad.Strong-bisimilarity as Strong
  using (Strongly-bisimilar; ∞Strongly-bisimilar; _∼_;
         now-cong; later-cong; force)
open import Delay-monad.Weak-bisimilarity as Weak
  using (Weakly-bisimilar; ∞Weakly-bisimilar; _≈_;
         now-cong; later-cong; laterˡ; laterʳ; force)

------------------------------------------------------------------------
-- The expansion relation

-- The expansion relation, defined using mixed induction and
-- coinduction.

mutual

  data Expansion (i : Size) : (x y : Delay A ∞) → Set a where
    now-cong   : ∀ {x} → Expansion i (now x) (now x)
    later-cong : ∀ {x y} →
                 ∞Expansion i (force x) (force y) →
                 Expansion i (later x) (later y)
    laterˡ     : ∀ {x y} →
                 Expansion i (force x) y →
                 Expansion i (later x) y

  record ∞Expansion (i : Size) (x y : Delay A ∞) : Set a where
    coinductive
    field
      force : {j : Size< i} → Expansion j x y

open ∞Expansion public

infix 4 _≳_ _∞≳_ _≲_ _∞≲_

_≳_ _∞≳_ _≲_ _∞≲_ : Delay A ∞ → Delay A ∞ → Set a
_≳_  = Expansion ∞
_∞≳_ = ∞Expansion ∞
_≲_  = flip _≳_
_∞≲_ = flip _∞≳_

------------------------------------------------------------------------
-- Conversion lemmas

mutual

  -- Strong bisimilarity is contained in the expansion relation.

  ∼→≳ : ∀ {i x y} → Strongly-bisimilar i x y → Expansion i x y
  ∼→≳ now-cong       = now-cong
  ∼→≳ (later-cong p) = later-cong (∞∼→≳ p)

  ∞∼→≳ : ∀ {i x y} → ∞Strongly-bisimilar i x y → ∞Expansion i x y
  force (∞∼→≳ p) = ∼→≳ (force p)

mutual

  -- The expansion relation is contained in weak bisimilarity.

  ≳→≈ : ∀ {i x y} → Expansion i x y → Weakly-bisimilar i x y
  ≳→≈ now-cong       = now-cong
  ≳→≈ (later-cong p) = later-cong (∞≳→≈ p)
  ≳→≈ (laterˡ p)     = laterˡ (≳→≈ p)

  ∞≳→≈ : ∀ {i x y} → ∞Expansion i x y → ∞Weakly-bisimilar i x y
  force (∞≳→≈ p) = ≳→≈ (force p)

-- In some cases weak bisimilarity is contained in the expansion
-- relation.

≈→≳-now :
  ∀ {i x y} → Weakly-bisimilar i x (now y) → Expansion i x (now y)
≈→≳-now now-cong   = now-cong
≈→≳-now (laterˡ p) = laterˡ (≈→≳-now p)

mutual

  ≈→≳-never :
    ∀ {i x} → Weakly-bisimilar i never x → Expansion i never x
  ≈→≳-never (later-cong p) = later-cong (∞≈→≳-never p)
  ≈→≳-never (laterˡ p)     = ≈→≳-never p
  ≈→≳-never (laterʳ p)     =
    later-cong (∞≈→≳-never (record { force = λ { {_} → p } }))

  ∞≈→≳-never :
    ∀ {i x} → ∞Weakly-bisimilar i never x → ∞Expansion i never x
  force (∞≈→≳-never p) = ≈→≳-never (force p)

-- In some cases the expansion relation is contained in strong
-- bisimilarity.

mutual

  ≳→∼-never :
    ∀ {i x} → Expansion i never x → Strongly-bisimilar i never x
  ≳→∼-never (later-cong p) = later-cong (∞≳→∼-never p)
  ≳→∼-never (laterˡ p)     = ≳→∼-never p

  ∞≳→∼-never :
    ∀ {i x} → ∞Expansion i never x → ∞Strongly-bisimilar i never x
  force (∞≳→∼-never p) = ≳→∼-never (force p)

------------------------------------------------------------------------
-- Some negative results

-- The computation never is not an expansion of now x.

never≵now : ∀ {i x} → ¬ Expansion i never (now x)
never≵now = Weak.now≉never ∘ Weak.symmetric ∘ ≳→≈

-- The computation now x is not an expansion of never.

now≵never : ∀ {i x} → ¬ Expansion i (now x) never
now≵never = Weak.now≉never ∘ ≳→≈

-- The expansion relation defined here is not pointwise propositional.

¬-≳-proposition : ¬ (∀ {x y} → Is-proposition (x ≳ y))
¬-≳-proposition =
  (∀ {x y} → Is-proposition (x ≳ y))  ↝⟨ (λ prop → _⇔_.to propositional⇔irrelevant (prop {x = never} {y = never})) ⟩
  Proof-irrelevant (never ≳ never)    ↝⟨ (λ irr → irr _ _) ⟩
  proof₁ ≡ proof₂                     ↝⟨ (λ ()) ⟩□
  ⊥₀                                  □
  where

  mutual

    proof₁ : never ≳ never
    proof₁ = later-cong ∞proof₁

    ∞proof₁ : never ∞≳ never
    force ∞proof₁ = proof₁

  proof₂ : never ≳ never
  proof₂ = laterˡ proof₁

------------------------------------------------------------------------
-- Sometimes one can remove later constructors

-- One can remove a later constructor to the right.

laterʳ⁻¹ : ∀ {i} {j : Size< i} {x y} →
           Expansion i x (later y) →
           Expansion j x (force y)
laterʳ⁻¹ (later-cong p) = laterˡ (force p)
laterʳ⁻¹ (laterˡ p)     = laterˡ (laterʳ⁻¹ p)

∞laterʳ⁻¹ : ∀ {i x y} →
            Expansion i x (later y) →
            ∞Expansion i x (force y)
force (∞laterʳ⁻¹ p) = laterʳ⁻¹ p

-- One can remove one later constructor on each side.

later⁻¹ : ∀ {i} {j : Size< i} {x y} →
          Expansion i (later x) (later y) →
          Expansion j (force x) (force y)
later⁻¹ (later-cong p) = force p
later⁻¹ (laterˡ p)     = laterʳ⁻¹ p

∞later⁻¹ : ∀ {i x y} →
           Expansion i (later x) (later y) →
           ∞Expansion i (force x) (force y)
force (∞later⁻¹ p) = later⁻¹ p

-- The following size-preserving variant of laterʳ⁻¹ can be defined.
--
-- Several other later-removing lemmas cannot be defined (unless A is
-- uninhabited), see below.

laterˡʳ⁻¹ :
  ∀ {i} {x y : ∞Delay A ∞} →
  Expansion i (later x) (force y) →
  Expansion i (force x) (later y) →
  Expansion i (force x) (force y)
laterˡʳ⁻¹ p q = laterˡʳ⁻¹′ p q refl refl
  where
  ∞laterˡʳ⁻¹′ :
    ∀ {i x′ y′} {x y : ∞Delay A ∞} →
    ∞Expansion i x′ (force y) →
    ∞Expansion i (force x) y′ →
    later x ≡ x′ → later y ≡ y′ →
    ∞Expansion i (force x) (force y)
  force (∞laterˡʳ⁻¹′ p q refl refl) = laterˡʳ⁻¹ (force p) (force q)

  laterˡʳ⁻¹′ :
    ∀ {i x′ y′} {x y : ∞Delay A ∞} →
    Expansion i (later x) y′ →
    Expansion i x′ (later y) →
    x′ ≡ force x → y′ ≡ force y →
    Expansion i x′ y′
  laterˡʳ⁻¹′ (later-cong p) (later-cong q) x′≡  y′≡  = later-cong (∞laterˡʳ⁻¹′ p q             x′≡ y′≡)
  laterˡʳ⁻¹′ (later-cong p) (laterˡ q)     x′≡  y′≡  = later-cong (∞laterˡʳ⁻¹′ p (∞laterʳ⁻¹ q) x′≡ y′≡)
  laterˡʳ⁻¹′ (laterˡ p)     _              refl refl = p

∞laterˡʳ⁻¹ :
  ∀ {i} {x y : ∞Delay A ∞} →
  ∞Expansion i (later x) (force y) →
  ∞Expansion i (force x) (later y) →
  ∞Expansion i (force x) (force y)
force (∞laterˡʳ⁻¹ p q) = laterˡʳ⁻¹ (force p) (force q)

------------------------------------------------------------------------
-- The expansion relation is a partial order (up to weak bisimilarity)

mutual

  -- The expansion relation is reflexive.

  reflexive : (x : Delay A ∞) → x ≳ x
  reflexive (now x)   = now-cong
  reflexive (later x) = later-cong (∞reflexive (force x))

  ∞reflexive : (x : Delay A ∞) → x ∞≳ x
  force (∞reflexive x) = reflexive x

-- The expansion relation is antisymmetric (up to weak bisimilarity).

antisymmetric :
  ∀ {i} {x y : Delay A ∞} →
  Expansion i x y → Expansion i y x → Weakly-bisimilar i x y
antisymmetric p _ = ≳→≈ p

mutual

  -- The expansion relation is transitive.

  transitive : ∀ {i} {x y z : Delay A ∞} →
               x ≳ y → Expansion i y z → Expansion i x z
  transitive {x = now x}   now-cong now-cong = now-cong
  transitive {x = later x} p        q        = later-trans p q
    where
    later-trans : ∀ {i x} {y z : Delay A ∞} →
                  later x ≳ y → Expansion i y z → Expansion i (later x) z
    later-trans p          (later-cong q) = later-cong (∞transitive (later⁻¹ p) q)
    later-trans p          (laterˡ q)     = later-trans (laterʳ⁻¹ p) q
    later-trans (laterˡ p) q              = laterˡ (transitive p q)

  ∞transitive : ∀ {i} {x y z : Delay A ∞} →
                x ≳ y → ∞Expansion i y z → ∞Expansion i x z
  force (∞transitive p q) = transitive p (force q)

-- Some size-preserving variants of transitivity.
--
-- Many size-preserving variants cannot be defined (unless A is
-- uninhabited), see below.

mutual

  transitive-≳∼ :
    ∀ {i} {x y z : Delay A ∞} →
    Expansion i x y → Strongly-bisimilar i y z → Expansion i x z
  transitive-≳∼ now-cong       now-cong       = now-cong
  transitive-≳∼ (later-cong p) (later-cong q) = later-cong (∞transitive-≳∼ p q)
  transitive-≳∼ (laterˡ p)     q              = laterˡ (transitive-≳∼ p q)

  ∞transitive-≳∼ :
    ∀ {i} {x y z : Delay A ∞} →
    ∞Expansion i x y → ∞Strongly-bisimilar i y z → ∞Expansion i x z
  force (∞transitive-≳∼ p q) = transitive-≳∼ (force p) (force q)

transitive-∼≳ :
  ∀ {i} {x y z : Delay A ∞} →
  x ∼ y → Expansion i y z → Expansion i x z
transitive-∼≳ = transitive ∘ ∼→≳

mutual

  transitive-≳≈ :
    ∀ {i} {x y z : Delay A ∞} →
    x ≳ y → Weakly-bisimilar i y z → Weakly-bisimilar i x z
  transitive-≳≈ {x = now x}   now-cong q = q
  transitive-≳≈ {x = later x} p        q = later-trans p q
    where
    later-trans : ∀ {i x} {y z : Delay A ∞} →
                  later x ≳ y → Weakly-bisimilar i y z →
                  Weakly-bisimilar i (later x) z
    later-trans p              (later-cong q) = later-cong (∞transitive-≳≈ (later⁻¹ p) q)
    later-trans p              (laterˡ q)     = later-trans (laterʳ⁻¹ p) q
    later-trans (later-cong p) (laterʳ q)     = later-cong (∞transitive-≳≈ (force p) (Weak.∞laterˡ⁻¹ q))
    later-trans (laterˡ p)     q              = laterˡ (transitive-≳≈ p q)

  ∞transitive-≳≈ :
    ∀ {i} {x y z : Delay A ∞} →
    x ≳ y → ∞Weakly-bisimilar i y z → ∞Weakly-bisimilar i x z
  force (∞transitive-≳≈ p q) = transitive-≳≈ p (force q)

-- Some special cases of symmetry hold.

mutual

  symmetric-neverˡ :
    ∀ {i x} → Expansion i never x → Expansion i x never
  symmetric-neverˡ (later-cong p) = later-cong (∞symmetric-neverˡ p)
  symmetric-neverˡ (laterˡ p)     = symmetric-neverˡ p

  ∞symmetric-neverˡ :
    ∀ {i x} → ∞Expansion i never x → ∞Expansion i x never
  force (∞symmetric-neverˡ p) = symmetric-neverˡ (force p)

mutual

  symmetric-neverʳ :
    ∀ {i x} → Expansion i x never → Expansion i never x
  symmetric-neverʳ (later-cong p) = later-cong (∞symmetric-neverʳ p)
  symmetric-neverʳ (laterˡ p)     =
    later-cong (∞symmetric-neverʳ (record { force = λ { {_} → p } }))

  ∞symmetric-neverʳ :
    ∀ {i x} → ∞Expansion i x never → ∞Expansion i never x
  force (∞symmetric-neverʳ p) = symmetric-neverʳ (force p)

------------------------------------------------------------------------
-- Lemmas stating that functions of certain types can be defined iff A
-- is uninhabited

mutual

  -- A lemma used in several of the proofs below: If A is uninhabited,
  -- then the expansion relation is trivial.

  uninhabited→trivial : ∀ {i} → ¬ A → ∀ x y → Expansion i x y
  uninhabited→trivial ¬A (now x)   _         = ⊥-elim (¬A x)
  uninhabited→trivial ¬A (later x) (now y)   = ⊥-elim (¬A y)
  uninhabited→trivial ¬A (later x) (later y) =
    later-cong (∞uninhabited→trivial ¬A x y)

  ∞uninhabited→trivial :
    ∀ {i} → ¬ A → ∀ x y → ∞Expansion i (force x) (force y)
  force (∞uninhabited→trivial ¬A x y) =
    uninhabited→trivial ¬A (force x) (force y)

-- There is a function that removes a later constructor to the left,
-- for computations of specific forms, iff A is uninhabited.

Laterˡ⁻¹′ = ∀ {x} →
            later (record { force = now x }) ≳
            later (record { force = now x }) →
            now x ≳ later (record { force = now x })

laterˡ⁻¹′⇔uninhabited : Laterˡ⁻¹′ ⇔ ¬ A
laterˡ⁻¹′⇔uninhabited = record
  { to = Laterˡ⁻¹′                        ↝⟨ (λ hyp _ → hyp) ⟩
         (∀ x → y x ≳ y x → now x ≳ y x)  ↝⟨ (λ hyp x → hyp x (reflexive _)) ⟩
         (∀ x → now x ≳ y x)              ↝⟨ (λ hyp x → now-x≵y x (hyp x)) ⟩□
         ¬ A                              □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ hyp {_} _ → hyp _ _) ⟩□
           Laterˡ⁻¹′        □
  }
  where
  module _ (x : A) where

    y : Delay A ∞
    y = later _

    now-x≵y : ¬ now x ≳ y
    now-x≵y ()

-- There is a function that removes a later constructor to the left
-- iff A is uninhabited.

Laterˡ⁻¹ = ∀ {x y} → later x ≳ y → force x ≳ y

laterˡ⁻¹⇔uninhabited : Laterˡ⁻¹ ⇔ ¬ A
laterˡ⁻¹⇔uninhabited = record
  { to = Laterˡ⁻¹   ↝⟨ (λ hyp → hyp) ⟩
         Laterˡ⁻¹′  ↝⟨ _⇔_.to laterˡ⁻¹′⇔uninhabited ⟩
         ¬ A        □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ hyp {_ _} _ → hyp _ _) ⟩□
           Laterˡ⁻¹         □
  }

-- The following variants of transitivity can be proved iff A is
-- uninhabited.

Transitivity-≈≳ = {x y z : Delay A ∞} → x ≈ y → y ≳ z → x ≳ z
Transitivity-≳≈ = {x y z : Delay A ∞} → x ≳ y → y ≈ z → x ≳ z

transitive-≈≳⇔uninhabited : Transitivity-≈≳ ⇔ ¬ A
transitive-≈≳⇔uninhabited = record
  { to = Transitivity-≈≳  ↝⟨ (λ trans → trans (laterʳ (Weak.reflexive _))) ⟩
         Laterˡ⁻¹         ↝⟨ _⇔_.to laterˡ⁻¹⇔uninhabited ⟩□
         ¬ A              □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ hyp {_ _ _} _ _ → hyp _ _) ⟩□
           Transitivity-≈≳  □
  }

transitive-≳≈⇔uninhabited : Transitivity-≳≈ ⇔ ¬ A
transitive-≳≈⇔uninhabited = record
  { to = Transitivity-≳≈  ↝⟨ (λ trans {_ y} lx≳y → later⁻¹ {y = record { force = y }}
                                                           (trans lx≳y (laterʳ (Weak.reflexive _)))) ⟩
         Laterˡ⁻¹         ↝⟨ _⇔_.to laterˡ⁻¹⇔uninhabited ⟩□
         ¬ A              □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ hyp {_ _ _} _ _ → hyp _ _) ⟩□
           Transitivity-≳≈  □
  }

------------------------------------------------------------------------
-- Lemmas stating that size-preserving functions of certain types can
-- be defined iff A is uninhabited

-- A variant of laterʳ⁻¹ in which one occurrence of the expansion
-- relation is replaced by strong bisimilarity, and both arguments are
-- specialised, can be made size-preserving iff A is uninhabited.

Laterʳ⁻¹-∼≳ =
  ∀ {i x} →
  Strongly-bisimilar i never (later (record { force = now x })) →
  Expansion i never (now x)

size-preserving-laterʳ⁻¹-∼≳⇔uninhabited : Laterʳ⁻¹-∼≳ ⇔ ¬ A
size-preserving-laterʳ⁻¹-∼≳⇔uninhabited = record
  { to   = Laterʳ⁻¹-∼≳       ↝⟨ ≳→≈ ∘_ ⟩
           Weak.Laterʳ⁻¹-∼≈  ↝⟨ _⇔_.to Weak.size-preserving-laterʳ⁻¹-∼≈⇔uninhabited ⟩□
           ¬ A               □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ trivial {_ _} _ → trivial _ _) ⟩□
           Laterʳ⁻¹-∼≳      □
  }

-- The function laterʳ⁻¹ can be made size-preserving iff A is
-- uninhabited.

Laterʳ⁻¹ = ∀ {i x y} →
           Expansion i x (later y) →
           Expansion i x (force y)

size-preserving-laterʳ⁻¹⇔uninhabited : Laterʳ⁻¹ ⇔ ¬ A
size-preserving-laterʳ⁻¹⇔uninhabited = record
  { to   = Laterʳ⁻¹     ↝⟨ _∘ ∼→≳ ⟩
           Laterʳ⁻¹-∼≳  ↝⟨ _⇔_.to size-preserving-laterʳ⁻¹-∼≳⇔uninhabited ⟩□
           ¬ A          □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ trivial {_ _ _} _ → trivial _ _) ⟩□
           Laterʳ⁻¹         □
  }

-- There is a variant of transitive-∼≳ that preserves the size of the
-- first argument iff A is uninhabited.

Transitivity-∼≳ˡ = ∀ {i} {x y z : Delay A ∞} →
                   Strongly-bisimilar i x y → y ≳ z → Expansion i x z

size-preserving-transitivity-∼≳ˡ⇔uninhabited : Transitivity-∼≳ˡ ⇔ ¬ A
size-preserving-transitivity-∼≳ˡ⇔uninhabited = record
  { to   = Transitivity-∼≳ˡ  ↝⟨ (λ trans never∼lnx → trans never∼lnx (laterˡ now-cong) ) ⟩
           Laterʳ⁻¹-∼≳       ↝⟨ _⇔_.to size-preserving-laterʳ⁻¹-∼≳⇔uninhabited ⟩□
           ¬ A               □
  ; from = ¬ A               ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)   ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-∼≳ˡ  □
  }

-- There is a transitivity proof that preserves the size of the
-- first argument iff A is uninhabited.

Transitivityˡ = ∀ {i} {x y z : Delay A ∞} →
                Expansion i x y → y ≳ z → Expansion i x z

size-preserving-transitivityˡ⇔uninhabited : Transitivityˡ ⇔ ¬ A
size-preserving-transitivityˡ⇔uninhabited = record
  { to   = Transitivityˡ     ↝⟨ _∘ ∼→≳ ⟩
           Transitivity-∼≳ˡ  ↝⟨ _⇔_.to size-preserving-transitivity-∼≳ˡ⇔uninhabited ⟩□
           ¬ A               □
  ; from = ¬ A              ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x ≳ y)  ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivityˡ    □
  }

-- There is a variant of transitive-≳≈ that preserves the size of the
-- first argument iff A is uninhabited.

Transitivity-≳≈ˡ =
  ∀ {i} {x y z : Delay A ∞} →
  Expansion i x y → y ≈ z → Weakly-bisimilar i x z

size-preserving-transitivity-≳≈ˡ⇔uninhabited : Transitivity-≳≈ˡ ⇔ ¬ A
size-preserving-transitivity-≳≈ˡ⇔uninhabited = record
  { to   = Transitivity-≳≈ˡ       ↝⟨ _∘ ∼→≳ ⟩
           Weak.Transitivity-∼≈ˡ  ↝⟨ _⇔_.to Weak.size-preserving-transitivity-∼≈ˡ⇔uninhabited ⟩
           ¬ A                    □
  ; from = ¬ A               ↝⟨ Weak.uninhabited→trivial ⟩
           (∀ x y → x ≈ y)   ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-≳≈ˡ  □
  }

-- More lemmas of a similar kind.

Transitivity-≈≲ʳ =
  ∀ {i} {x y z : Delay A ∞} →
  x ≈ y → Expansion i z y → Weakly-bisimilar i x z

size-preserving-transitivity-≈≲ʳ⇔uninhabited : Transitivity-≈≲ʳ ⇔ ¬ A
size-preserving-transitivity-≈≲ʳ⇔uninhabited =
  Transitivity-≈≲ʳ  ↝⟨ record { to   = λ trans x≳y y≈z → Weak.symmetric (trans (Weak.symmetric y≈z) x≳y)
                              ; from = λ trans x≈y y≲z → Weak.symmetric (trans y≲z (Weak.symmetric x≈y))
                              } ⟩
  Transitivity-≳≈ˡ  ↝⟨ size-preserving-transitivity-≳≈ˡ⇔uninhabited ⟩□
  ¬ A               □

Transitivity-≈≳ˡ =
  ∀ {i} {x y z : Delay A ∞} →
  Weakly-bisimilar i x y → y ≳ z → Weakly-bisimilar i x z

size-preserving-transitivity-≈≳ˡ⇔uninhabited : Transitivity-≈≳ˡ ⇔ ¬ A
size-preserving-transitivity-≈≳ˡ⇔uninhabited = record
  { to   = Transitivity-≈≳ˡ  ↝⟨ (λ trans x≈ly → trans x≈ly (laterˡ (reflexive _))) ⟩
           Weak.Laterʳ⁻¹     ↝⟨ _⇔_.to Weak.size-preserving-laterʳ⁻¹⇔uninhabited ⟩
           ¬ A               □
  ; from = ¬ A               ↝⟨ Weak.uninhabited→trivial ⟩
           (∀ x y → x ≈ y)   ↝⟨ (λ trivial {_ _ _ _} _ _ → trivial _ _) ⟩□
           Transitivity-≈≳ˡ  □
  }
