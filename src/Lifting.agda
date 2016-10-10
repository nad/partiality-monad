------------------------------------------------------------------------
-- A higher inductive-inductive definition of the lifting construction
-- on ω-CPOs
------------------------------------------------------------------------

-- Note that this module is experimental: it uses postulates to encode
-- a higher inductive-inductive type.

{-# OPTIONS --without-K #-}

open import Omega-CPO

module Lifting {ℓ} (cpo : ω-CPO ℓ) where

open import Equality.Propositional
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J hiding (_∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J

private
  module CPO = ω-CPO cpo

------------------------------------------------------------------------
-- An ω-CPPO

-- The carrier type (Carrier) and the information ordering (_⊑_) are
-- defined simultaneously.

infix 4 _⊑_ _⊒_

postulate
  Carrier : Set ℓ
  _⊑_     : Carrier → Carrier → Set ℓ

_⊒_ : Carrier → Carrier → Set ℓ
x ⊒ y = y ⊑ x

-- Increasing sequences.

Increasing-sequence : Set ℓ
Increasing-sequence = ∃ λ (f : ℕ → Carrier) → ∀ n → f n ⊑ f (suc n)

-- Projection functions for Increasing-sequence.

infix 30 _[_]

_[_] : Increasing-sequence → ℕ → Carrier
_[_] = proj₁

increasing : (s : Increasing-sequence) →
             ∀ n → s [ n ] ⊑ s [ suc n ]
increasing = proj₂

-- Upper bounds.

Is-upper-bound : Increasing-sequence → Carrier → Set ℓ
Is-upper-bound s x = ∀ n → s [ n ] ⊑ x

postulate

  -- _⊥ "constructors".

  never        : Carrier
  now          : CPO.Carrier → Carrier
  ⨆            : Increasing-sequence → Carrier
  antisymmetry : ∀ {x y} → x ⊑ y → x ⊒ y → x ≡ y

private
  postulate

    -- We have chosen to explicitly make the type set-truncated.
    -- However, this "constructor" is private in order to highlight
    -- that it is not used anywhere in the development.
    ≡-proof-irrelevant : {x y : Carrier} → Proof-irrelevant (x ≡ y)

postulate

  -- _⊑_ "constructors".

  ⊑-refl             : ∀ x → x ⊑ x
  ⊑-trans            : ∀ x y z → x ⊑ y → y ⊑ z → x ⊑ z
  never⊑             : ∀ x → never ⊑ x
  upper-bound        : ∀ s → Is-upper-bound s (⨆ s)
  least-upper-bound  : ∀ s ub → Is-upper-bound s ub → ⨆ s ⊑ ub
  now-mono           : ∀ {x y} → x CPO.⊑ y → now x ⊑ now y
  now-⨆′             : ∀ s →
                       now (CPO.⨆ s) ⊑ ⨆ (Σ-map (now ∘_) (now-mono ∘_) s)
  ⊑-proof-irrelevant : ∀ {x y} → Proof-irrelevant (x ⊑ y)

-- The construction above is an ω-CPPO.

cppo : ω-CPPO ℓ
cppo = record
  { cpo = record
    { Carrier           = Carrier
    ; _⊑_               = _⊑_
    ; reflexivity       = ⊑-refl _
    ; antisymmetry      = antisymmetry
    ; transitivity      = ⊑-trans _ _ _
    ; ⨆                 = ⨆
    ; upper-bound       = upper-bound
    ; least-upper-bound = least-upper-bound _ _
    }
  ; least  = never
  ; least⊑ = never⊑ _
  }

------------------------------------------------------------------------
-- Dependent eliminators

-- Predicate transformer related to increasing sequences.

Inc : ∀ {p q}
      (P : Carrier → Set p)
      (Q : ∀ {x y} → P x → P y → x ⊑ y → Set q) →
      Increasing-sequence → Set (p ⊔ q)
Inc P Q s =
  ∃ λ (p : ∀ n → P (s [ n ])) →
    ∀ n → Q (p n) (p (suc n)) (increasing s n)

-- Record wrapping up the eliminators' arguments.

record Rec-args
         {p q}
         (P : Carrier → Set p)
         (Q : ∀ {x y} → P x → P y → x ⊑ y → Set q) :
         Set (ℓ ⊔ p ⊔ q) where
  field
    pe : P never
    po : ∀ x → P (now x)
    pl : ∀ s (pq : Inc P Q s) → P (⨆ s)
    pa : ∀ {x y} (x⊑y : x ⊑ y) (x⊒y : x ⊒ y)
         (p-x : P x) (p-y : P y)
         (q-x⊑y : Q p-x p-y x⊑y) (q-x⊒y : Q p-y p-x x⊒y) →
         subst P (antisymmetry x⊑y x⊒y) p-x ≡ p-y
    pp : ∀ {x} {p₁ p₂ : P x} → Proof-irrelevant (p₁ ≡ p₂)
    qr : ∀ x (p : P x) → Q p p (⊑-refl x)
    qt : ∀ {x y z}
         (x⊑y : x ⊑ y) (y⊑z : y ⊑ z)
         (p-x : P x) (p-y : P y) (p-z : P z) →
         Q p-x p-y x⊑y → Q p-y p-z y⊑z →
         Q p-x p-z (⊑-trans x y z x⊑y y⊑z)
    qe : ∀ x (p : P x) → Q pe p (never⊑ x)
    qu : ∀ s (pq : Inc P Q s) n →
         Q (proj₁ pq n) (pl s pq) (upper-bound s n)
    ql : ∀ s ub is-ub (pq : Inc P Q s) (pu : P ub)
         (qu : ∀ n → Q (proj₁ pq n) pu (is-ub n)) →
         Q (pl s pq) pu (least-upper-bound s ub is-ub)
    qm : ∀ {x y} (le : x CPO.⊑ y) →
         Q (po x) (po y) (now-mono le)
    q⨆ : ∀ s →
         Q (po (CPO.⨆ s))
           (pl (Σ-map (now ∘_) (now-mono ∘_) s)
               ( (λ n → po (s CPO.[ n ]))
               , (λ n → qm (CPO.increasing s n))
               ))
           (now-⨆′ s)
    qp : ∀ {x y} (p-x : P x) (p-y : P y) (x⊑y : x ⊑ y) →
         Proof-irrelevant (Q p-x p-y x⊑y)

-- The eliminators.

module _ {p q}
         {P : Carrier → Set p}
         {Q : ∀ {x y} → P x → P y → x ⊑ y → Set q}
         (args : Rec-args P Q) where

  open Rec-args args

  postulate
    ⊥-rec : (x : Carrier) → P x
    ⊑-rec : ∀ {x y} (x⊑y : x ⊑ y) → Q (⊥-rec x) (⊥-rec y) x⊑y

  inc-rec : (s : Increasing-sequence) → Inc P Q s
  inc-rec (s , inc) = ( (λ n → ⊥-rec (s   n))
                      , (λ n → ⊑-rec (inc n))
                      )

  -- Some "computation" rules.

  postulate

    ⊥-rec-never : ⊥-rec never ≡ pe
    ⊥-rec-now   : ∀ x → ⊥-rec (now x) ≡ po x
    ⊥-rec-⨆     : ∀ s → ⊥-rec (⨆ s) ≡ pl s (inc-rec s)

------------------------------------------------------------------------
-- Some lemmas

-- The inequality now-⨆′ can be strengthened to an equality.

now-⨆ : (s : CPO.Increasing-sequence) →
        now (CPO.⨆ s) ≡ ⨆ (Σ-map (now ∘_) (now-mono ∘_) s)
now-⨆ s =
  antisymmetry
    (now-⨆′ s)
    (least-upper-bound _ _ λ n → now-mono (CPO.upper-bound s n))

-- The information ordering is propositional.

⊑-propositional : ∀ {x y} → Is-proposition (x ⊑ y)
⊑-propositional = _⇔_.from propositional⇔irrelevant ⊑-proof-irrelevant

private

  -- A lemma.

  Carrier-is-set-and-equality-characterisation : Is-set Carrier × _
  Carrier-is-set-and-equality-characterisation =
    Eq.propositional-identity≃≡
      (λ x y → x ⊑ y × x ⊒ y)
      (λ _ _ → ×-closure 1 ⊑-propositional ⊑-propositional)
      (λ x → ⊑-refl x , ⊑-refl x)
      (λ x y → uncurry {B = λ _ → x ⊒ y} antisymmetry)

-- Carrier is a set. (This lemma is analogous to Theorem 11.3.9 in
-- "Homotopy Type Theory: Univalent Foundations of Mathematics" (first
-- edition).)

Carrier-is-set : Is-set Carrier
Carrier-is-set = proj₁ Carrier-is-set-and-equality-characterisation

-- Equality characterisation lemma for Carrier.

equality-characterisation-Carrier :
  ∀ {x y} → (x ⊑ y × x ⊒ y) ≃ (x ≡ y)
equality-characterisation-Carrier =
  proj₂ Carrier-is-set-and-equality-characterisation ext

-- Equality characterisation lemma for increasing sequences.

equality-characterisation-increasing :
  {s₁ s₂ : Increasing-sequence} →
  (∀ n → s₁ [ n ] ≡ s₂ [ n ]) ↔ s₁ ≡ s₂
equality-characterisation-increasing {s₁} {s₂} =
  (∀ n → s₁ [ n ] ≡ s₂ [ n ])  ↔⟨ Eq.extensionality-isomorphism ext ⟩
  proj₁ s₁ ≡ proj₁ s₂          ↝⟨ ignore-propositional-component
                                    (Π-closure ext 1 λ _ →
                                     ⊑-propositional) ⟩□
  s₁ ≡ s₂                      □
