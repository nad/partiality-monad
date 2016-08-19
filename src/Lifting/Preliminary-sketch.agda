------------------------------------------------------------------------
-- A partial inductive-recursive definition of the lifting
-- construction on ω-CPOs, without path or truncation constructors, in
-- order to get the basics right
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Omega-CPO

module Lifting.Preliminary-sketch {ℓ} (cpo : ω-CPO ℓ) where

open import Prelude hiding (⊥)

private
  module CPO = ω-CPO cpo

-- The carrier type (Carrier) and the information ordering (_⊑_) are
-- defined as a single inductive family D. A boolean index is used to
-- separate the two types. I (NAD) think that Conor McBride once
-- pointed out that inductive-inductive types can be encoded as
-- inductive-recursive types in (roughly) the following way.

I : Bool → Set ℓ

data D : (b : Bool) → I b → Set ℓ

infix 4 _⊑_

Carrier : Set ℓ
_⊑_     : Carrier → Carrier → Set ℓ

-- Carrier is not indexed, but _⊑_ is indexed by two values of type
-- Carrier.

I true  = ↑ _ ⊤
I false = Carrier × Carrier

Carrier = D true _

x ⊑ y = D false (x , y)

-- Increasing sequences.

Increasing-sequence : Set ℓ
Increasing-sequence = ∃ λ (f : ℕ → Carrier) → ∀ n → f n ⊑ f (suc n)

-- Projection functions for Increasing-sequence.

infix 30 _[_]

_[_] : Increasing-sequence → ℕ → Carrier
_[_] = proj₁

increasing : (s : Increasing-sequence) → ∀ n → s [ n ] ⊑ s [ suc n ]
increasing = proj₂

-- Upper bounds.

Is-upper-bound : Increasing-sequence → Carrier → Set ℓ
Is-upper-bound s x = ∀ n → s [ n ] ⊑ x

-- _⊥ and _⊑_.

data D where
  never : Carrier
  now   : CPO.Carrier → Carrier
  ⨆     : Increasing-sequence → Carrier

  ⊑-refl            : ∀ x → x ⊑ x
  ⊑-trans           : ∀ x y z → x ⊑ y → y ⊑ z → x ⊑ z
  never⊑            : ∀ x → never ⊑ x
  upper-bound       : ∀ s → Is-upper-bound s (⨆ s)
  least-upper-bound : ∀ s ub → (is-ub : Is-upper-bound s ub) → ⨆ s ⊑ ub
  now-mono          : ∀ {x y} → x CPO.⊑ y → now x ⊑ now y
  now-⨆′            : ∀ s →
                      now (CPO.⨆ s) ⊑ ⨆ (Σ-map (now ∘_) (now-mono ∘_) s)

-- Predicate transformer related to increasing sequences.

Inc : ∀ {p q}
      (P : Carrier → Set p) →
      (∀ {x y} → P x → P y → x ⊑ y → Set q) →
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

-- Mutually defined dependent eliminators.

module _
  {p q}
  {P : Carrier → Set p}
  {Q : ∀ {x y} → P x → P y → x ⊑ y → Set q}
  (args : Rec-args P Q)
  where

  open Rec-args args

  ⊥-rec   : (x : Carrier) → P x
  inc-rec : (s : Increasing-sequence) → Inc P Q s
  ⊑-rec   : ∀ {x y} (x⊑y : x ⊑ y) → Q (⊥-rec x) (⊥-rec y) x⊑y

  ⊥-rec never   = pe
  ⊥-rec (now x) = po x
  ⊥-rec (⨆ s)   = pl s (inc-rec s)

  inc-rec (s , inc) = ( (λ n → ⊥-rec (s   n))
                      , (λ n → ⊑-rec (inc n))
                      )

  ⊑-rec (⊑-refl x)                     = qr x (⊥-rec x)
  ⊑-rec (⊑-trans x y z x⊑y y⊑z)        = qt x⊑y y⊑z
                                            (⊥-rec x) (⊥-rec y) (⊥-rec z)
                                            (⊑-rec x⊑y) (⊑-rec y⊑z)
  ⊑-rec (never⊑ x)                     = qe x (⊥-rec x)
  ⊑-rec (upper-bound s n)              = qu s (inc-rec s) n
  ⊑-rec (least-upper-bound s ub is-ub) = ql s ub is-ub
                                            (inc-rec s) (⊥-rec ub)
                                            (λ n → ⊑-rec (is-ub n))
  ⊑-rec (now-mono le)                  = qm le
  ⊑-rec (now-⨆′ s)                     = q⨆ s
