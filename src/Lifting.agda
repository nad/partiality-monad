------------------------------------------------------------------------
-- A quotient inductive-inductive definition of the lifting
-- construction on ω-cpos
------------------------------------------------------------------------

-- The code in this module is based on a suggestion from Paolo
-- Capriotti.

{-# OPTIONS --erased-cubical --safe #-}

open import Omega-cpo

module Lifting {ℓ} (cpo : ω-cpo ℓ ℓ) where

import Equality.Path as P
open import Equality.Propositional.Cubical
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J hiding (_∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J

private
  module CPO = ω-cpo cpo

------------------------------------------------------------------------
-- An ω-cppo

-- The carrier type (Carrier) and the information ordering (_⊑_) are
-- defined simultaneously.

infix 4 _⊑_ _⊒_

data Carrier : Type ℓ
data _⊑_     : Carrier → Carrier → Type ℓ

_⊒_ : Carrier → Carrier → Type ℓ
x ⊒ y = y ⊑ x

private
  variable
    x y : Carrier

-- Increasing sequences.

Increasing-sequence : Type ℓ
Increasing-sequence = ∃ λ (f : ℕ → Carrier) → ∀ n → f n ⊑ f (suc n)

-- Projection functions for Increasing-sequence.

infix 30 _[_]

_[_] : Increasing-sequence → ℕ → Carrier
_[_] = proj₁

increasing : (s : Increasing-sequence) →
             ∀ n → s [ n ] ⊑ s [ suc n ]
increasing = proj₂

-- Upper bounds.

Is-upper-bound : Increasing-sequence → Carrier → Type ℓ
Is-upper-bound s x = ∀ n → s [ n ] ⊑ x

-- Originally these types were postulated. After the release of
-- Cubical Agda they were turned into a QIIT, but in order to not get
-- any extra computation rules they were made abstract.

abstract

  -- _⊥ "constructors".

  data Carrier where
    never′        : Carrier
    now′          : CPO.Carrier → Carrier
    ⨆′            : Increasing-sequence → Carrier
    antisymmetry′ : x ⊑ y → x ⊒ y → x P.≡ y

    -- We have chosen to explicitly make the type set-truncated.
    -- However, this constructor is only used in the definition of the
    -- eliminator below.
    ≡-propositional′ : P.Is-set Carrier

  -- _⊑_ "constructors".

  data _⊑_ where
    ⊑-refl′            : ∀ x → x ⊑ x
    ⊑-trans′           : ∀ x y z → x ⊑ y → y ⊑ z → x ⊑ z
    never⊑′            : ∀ x → never′ ⊑ x
    upper-bound′       : ∀ s → Is-upper-bound s (⨆′ s)
    least-upper-bound′ : ∀ s ub → Is-upper-bound s ub → ⨆′ s ⊑ ub
    now-mono′          : ∀ {x y} → x CPO.⊑ y → now′ x ⊑ now′ y
    now-⨆″             : ∀ s →
                         now′ (CPO.⨆ s) ⊑
                         ⨆′ (Σ-map (now′ ∘_) (now-mono′ ∘_) s)
    ⊑-propositional′   : ∀ {x y} → P.Is-proposition (x ⊑ y)

  never : Carrier
  never = never′

  now : CPO.Carrier → Carrier
  now = now′

  ⨆ : Increasing-sequence → Carrier
  ⨆ = ⨆′

  antisymmetry : x ⊑ y → y ⊑ x → x ≡ y
  antisymmetry = λ p q → _↔_.from ≡↔≡ (antisymmetry′ p q)

  ⊑-refl : ∀ x → x ⊑ x
  ⊑-refl = ⊑-refl′

  ⊑-trans : ∀ x y z → x ⊑ y → y ⊑ z → x ⊑ z
  ⊑-trans = ⊑-trans′

  never⊑ : ∀ x → never ⊑ x
  never⊑ = never⊑′

  upper-bound : ∀ s → Is-upper-bound s (⨆ s)
  upper-bound = upper-bound′

  least-upper-bound : ∀ s ub → Is-upper-bound s ub → ⨆ s ⊑ ub
  least-upper-bound = least-upper-bound′

  now-mono : ∀ {x y} → x CPO.⊑ y → now x ⊑ now y
  now-mono = now-mono′

  now-⨆′ : ∀ s → now (CPO.⨆ s) ⊑ ⨆ (Σ-map (now ∘_) (now-mono ∘_) s)
  now-⨆′ = now-⨆″

  ⊑-propositional : ∀ {x y} → Is-proposition (x ⊑ y)
  ⊑-propositional {x = x} {y = y} =
                              $⟨ ⊑-propositional′ ⟩
    P.Is-proposition (x ⊑ y)  ↝⟨ _↔_.from (H-level↔H-level 1) ⟩□
    Is-proposition (x ⊑ y)    □

-- The construction above is an ω-cppo.

cppo : ω-cppo ℓ ℓ
cppo = record
  { cpo = record
    { Carrier           = Carrier
    ; _⊑_               = _⊑_
    ; reflexivity       = ⊑-refl _
    ; antisymmetry      = antisymmetry
    ; transitivity      = ⊑-trans _ _ _
    ; ⊑-propositional   = ⊑-propositional
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
      (P : Carrier → Type p)
      (Q : ∀ {x y} → P x → P y → x ⊑ y → Type q) →
      Increasing-sequence → Type (p ⊔ q)
Inc P Q s =
  ∃ λ (p : ∀ n → P (s [ n ])) →
    ∀ n → Q (p n) (p (suc n)) (increasing s n)

-- Record wrapping up the eliminators' arguments.

record Rec-args
         {p q}
         (P : Carrier → Type p)
         (Q : ∀ {x y} → P x → P y → x ⊑ y → Type q) :
         Type (ℓ ⊔ p ⊔ q) where
  field
    pe : P never
    po : ∀ x → P (now x)
    pl : ∀ s (pq : Inc P Q s) → P (⨆ s)
    pa : ∀ {x y} (x⊑y : x ⊑ y) (x⊒y : x ⊒ y)
         (p-x : P x) (p-y : P y)
         (q-x⊑y : Q p-x p-y x⊑y) (q-x⊒y : Q p-y p-x x⊒y) →
         subst P (antisymmetry x⊑y x⊒y) p-x ≡ p-y
    pp : ∀ {x} {p₁ p₂ : P x} → Is-proposition (p₁ ≡ p₂)
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
         Is-proposition (Q p-x p-y x⊑y)

-- The eliminators.

module _ {p q}
         {P : Carrier → Type p}
         {Q : ∀ {x y} → P x → P y → x ⊑ y → Type q}
         (args : Rec-args P Q) where

  open Rec-args args

  mutual

    inc-rec : (s : Increasing-sequence) → Inc P Q s
    inc-rec (s , inc) = (λ n → ⊥-rec (s   n))
                      , (λ n → ⊑-rec (inc n))

    abstract

      ⊥-rec : (x : Carrier) → P x
      ⊥-rec never′ = pe

      ⊥-rec (now′ x) = po x

      ⊥-rec (⨆′ s) = pl s (inc-rec s)

      ⊥-rec (antisymmetry′ {x = x} {y = y} p q i) =
        subst≡→[]≡
          {B = P}
          {eq = antisymmetry′ p q}
          (pa p q (⊥-rec x) (⊥-rec y) (⊑-rec p) (⊑-rec q)) i

      ⊥-rec (≡-propositional′ {x = x} {y = y} p q i j) = lemma i j
        where
        ≡-propositional : P.Is-set Carrier
        ≡-propositional = ≡-propositional′

        lemma :
          P.[ (λ i → P.[ (λ j → P (≡-propositional p q i j)) ]
                       ⊥-rec x ≡ ⊥-rec y) ]
            (λ i → ⊥-rec (p i)) ≡ (λ i → ⊥-rec (q i))
        lemma = P.heterogeneous-UIP
                  (λ x → _↔_.to (H-level↔H-level 2) (pp {x = x}))
                  (≡-propositional′ p q)
                  _ _

      ⊑-rec : (x⊑y : x ⊑ y) → Q (⊥-rec x) (⊥-rec y) x⊑y
      ⊑-rec (⊑-refl′ x) = qr x (⊥-rec x)

      ⊑-rec (⊑-trans′ x y z p q) =
        qt p q (⊥-rec x) (⊥-rec y) (⊥-rec z) (⊑-rec p) (⊑-rec q)

      ⊑-rec (never⊑′ x) = qe x (⊥-rec x)

      ⊑-rec (upper-bound′ s n) = qu s (inc-rec s) n

      ⊑-rec (least-upper-bound′ s ub is-ub) =
        ql s ub is-ub (inc-rec s) (⊥-rec ub)
          (λ n → ⊑-rec {x = proj₁ s n} (is-ub n))

      ⊑-rec (now-mono′ x) = qm x

      ⊑-rec (now-⨆″ s) = q⨆ s

      ⊑-rec (⊑-propositional′ {x = x} {y = y} p q i) = lemma i
        where
        ⊑-propositional″ : ∀ {x y} → P.Is-proposition (x ⊑ y)
        ⊑-propositional″ = ⊑-propositional′

        lemma : P.[ (λ i → Q (⊥-rec x) (⊥-rec y)
                             (⊑-propositional″ p q i)) ]
                  ⊑-rec p ≡ ⊑-rec q
        lemma =
          P.heterogeneous-irrelevance
            (λ p → _↔_.to (H-level↔H-level 1)
                     (qp (⊥-rec x) (⊥-rec y) p))

      -- Some computation rules.

      ⊥-rec-never : ⊥-rec never ≡ pe
      ⊥-rec-never = refl

      ⊥-rec-now : ∀ x → ⊥-rec (now x) ≡ po x
      ⊥-rec-now _ = refl

      ⊥-rec-⨆ : ∀ s → ⊥-rec (⨆ s) ≡ pl s (inc-rec s)
      ⊥-rec-⨆ _ = refl

------------------------------------------------------------------------
-- Some lemmas

-- The inequality now-⨆′ can be strengthened to an equality.

now-⨆ : (s : CPO.Increasing-sequence) →
        now (CPO.⨆ s) ≡ ⨆ (Σ-map (now ∘_) (now-mono ∘_) s)
now-⨆ s =
  antisymmetry
    (now-⨆′ s)
    (least-upper-bound _ _ λ n → now-mono (CPO.upper-bound s n))

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
