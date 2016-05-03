------------------------------------------------------------------------
-- A higher inductive-inductive definition of the partiality monad
------------------------------------------------------------------------

-- Note that this module is experimental: it uses rewrite rules to
-- encode a higher inductive-inductive type.

-- This code is heavily inspired by the section on Cauchy reals in the
-- HoTT book (first edition).

{-# OPTIONS --without-K --rewriting #-}

module Partiality-monad.Inductive where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
import Nat
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Equality.Decidable-UIP equality-with-J
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional as Trunc
open import Interval using (ext)
import Monad
open import Surjection equality-with-J using (module _↠_)
open import Univalence-axiom equality-with-J

------------------------------------------------------------------------
-- First: A partial inductive definition of the partiality monad,
-- without path or truncation constructors, in order to get the basics
-- right
------------------------------------------------------------------------

private
 module Preliminary-sketch where

  -- The partiality monad _⊥ and the information ordering _⊑_ are
  -- defined as a single inductive family D. A boolean index is used
  -- to separate the two types. I (NAD) think that Conor McBride once
  -- pointed out that inductive-inductive types can be encoded as
  -- inductive-recursive types in (roughly) the following way.

  I : ∀ {a} → Set a → Bool → Set a

  data D {a} (A : Set a) : (b : Bool) → I A b → Set a

  infix 10 _⊥
  infix  4 _⊑_

  _⊥  : ∀ {a} → Set a → Set a
  _⊑_ : ∀ {a} {A : Set a} → A ⊥ → A ⊥ → Set a

  -- _⊥ is not indexed, but _⊑_ is indexed by two values of type A ⊥
  -- (for some A).

  I A true  = ↑ _ ⊤
  I A false = A ⊥ × A ⊥

  A ⊥ = D A true _

  x ⊑ y = D _ false (x , y)

  -- Increasing sequences.

  Increasing-sequence : ∀ {a} → Set a → Set a
  Increasing-sequence A = ∃ λ (f : ℕ → A ⊥) → ∀ n → f n ⊑ f (suc n)

  -- Projection functions for Increasing-sequence.

  infix 30 _[_]

  _[_] : ∀ {a} {A : Set a} → Increasing-sequence A → ℕ → A ⊥
  s [ n ] = proj₁ s n

  increasing : ∀ {a} {A : Set a}
               (s : Increasing-sequence A) →
               ∀ n → s [ n ] ⊑ s [ suc n ]
  increasing = proj₂

  -- Upper bounds.

  Is-upper-bound : ∀ {a} {A : Set a} →
                   Increasing-sequence A → A ⊥ → Set a
  Is-upper-bound s x = ∀ n → s [ n ] ⊑ x

  -- _⊥ and _⊑_.

  data D {a} (A : Set a) where
    never : A ⊥
    now   : (x : A) → A ⊥
    ⨆     : (s : Increasing-sequence A) → A ⊥

    ⊑-refl            : (x : A ⊥) → x ⊑ x
    never⊑            : (x : A ⊥) → never ⊑ x
    upper-bound′      : (s : Increasing-sequence A) (ub : A ⊥)
                        (is-ub : ⨆ s ⊑ ub) → Is-upper-bound s ub
    least-upper-bound : (s : Increasing-sequence A) (ub : A ⊥)
                        (is-ub : Is-upper-bound s ub) → ⨆ s ⊑ ub

  -- Some examples.

  -- ⨆ s is an upper bound for the sequence s.

  upper-bound : ∀ {a} {A : Set a}
                (s : Increasing-sequence A) →
                Is-upper-bound s (⨆ s)
  upper-bound s = upper-bound′ s (⨆ s) (⊑-refl (⨆ s))

  -- Transitivity.

  ⊑-trans : ∀ {a} {A : Set a} {x y z : A ⊥} → x ⊑ y → y ⊑ z → x ⊑ z
  ⊑-trans (⊑-refl y)                  y⊑z  = y⊑z
  ⊑-trans (never⊑ y)                  y⊑z  = never⊑ _
  ⊑-trans (upper-bound′ s ub is-ub n) ub⊑z =
    ⊑-trans (proj₂ s n) (upper-bound′ s _ (⊑-trans is-ub ub⊑z) (suc n))
  ⊑-trans (least-upper-bound s ub is-ub) ub⊑z =
    least-upper-bound s _ (λ n → ⊑-trans (is-ub n) ub⊑z)

  -- A monotone map function.

  I-map : ∀ {a b} {A : Set a} {B : Set b} →
          (f : A → B) → ∀ {b} → I A b → I B b

  Increasing-sequence-map :
    ∀ {a b} {A : Set a} {B : Set b} →
    (f : A → B) → Increasing-sequence A → Increasing-sequence B

  D-map : ∀ {a b} {A : Set a} {B : Set b} →
          (f : A → B) → ∀ {i b} → D A i b → D B i (I-map f b)

  I-map f {b = true}  _       = _
  I-map f {b = false} (x , y) = D-map f x , D-map f y

  Increasing-sequence-map f (s , inc) =
    (λ n → D-map f (s   n)) ,
    (λ n → D-map f (inc n))

  D-map f never                          = never
  D-map f (now x)                        = now (f x)
  D-map f (⨆ s)                          = ⨆ (Increasing-sequence-map f s)
  D-map f (⊑-refl x)                     = ⊑-refl (D-map f x)
  D-map f (never⊑ x)                     = never⊑ (D-map f x)
  D-map f (upper-bound′ s ub is-ub n)    = upper-bound′
                                             (Increasing-sequence-map f s)
                                             (D-map f ub)
                                             (D-map f is-ub)
                                             n
  D-map f (least-upper-bound s ub is-ub) = least-upper-bound
                                             (Increasing-sequence-map f s)
                                             (D-map f ub)
                                             (λ n → D-map f (is-ub n))

  -- Predicate transformer related to increasing sequences.

  Inc : ∀ {a p q} {A : Set a}
        (P : A ⊥ → Set p) →
        (∀ {x y} → P x → P y → x ⊑ y → Set q) →
        Increasing-sequence A → Set (p ⊔ q)
  Inc P Q s =
    ∃ λ (p : ∀ n → P (s [ n ])) →
      ∀ n → Q (p n) (p (suc n)) (increasing s n)

  -- Record wrapping up the eliminators' arguments.

  record Rec-args
           {a p q} {A : Set a}
           (P : A ⊥ → Set p)
           (Q : ∀ {x y} → P x → P y → x ⊑ y → Set q) :
           Set (a ⊔ p ⊔ q) where
    field
      pe : P never
      po : ∀ x → P (now x)
      pl : ∀ s (pq : Inc P Q s) → P (⨆ s)
      qr : ∀ x (p : P x) → Q p p (⊑-refl x)
      qe : ∀ x (p : P x) → Q pe p (never⊑ x)
      qu : ∀ s ub is-ub n (pq : Inc P Q s) (pu : P ub)
           (qu : Q (pl s pq) pu is-ub) →
           Q (proj₁ pq n) pu (upper-bound′ s ub is-ub n)
      ql : ∀ s ub is-ub (pq : Inc P Q s) (pu : P ub)
           (qu : ∀ n → Q (proj₁ pq n) pu (is-ub n)) →
           Q (pl s pq) pu (least-upper-bound s ub is-ub)

  -- Mutually defined dependent eliminators.

  module _
    {a p q} {A : Set a}
    {P : A ⊥ → Set p}
    {Q : ∀ {x y} → P x → P y → x ⊑ y → Set q}
    (args : Rec-args P Q)
    where

    open Rec-args args

    ⊥-rec   : (x : A ⊥) → P x
    inc-rec : (s : Increasing-sequence A) → Inc P Q s
    ⊑-rec   : ∀ {x y} (x⊑y : x ⊑ y) → Q (⊥-rec x) (⊥-rec y) x⊑y

    ⊥-rec never   = pe
    ⊥-rec (now x) = po x
    ⊥-rec (⨆ s)   = pl s (inc-rec s)

    inc-rec (s , inc) = ( (λ n → ⊥-rec (s   n))
                        , (λ n → ⊑-rec (inc n))
                        )

    ⊑-rec (⊑-refl x)                     = qr x (⊥-rec x)
    ⊑-rec (never⊑ x)                     = qe x (⊥-rec x)
    ⊑-rec (upper-bound′ s ub is-ub n)    = qu s ub is-ub n
                                              (inc-rec s) (⊥-rec ub)
                                              (⊑-rec is-ub)
    ⊑-rec (least-upper-bound s ub is-ub) = ql s ub is-ub
                                              (inc-rec s) (⊥-rec ub)
                                              (λ n → ⊑-rec (is-ub n))

  -- These dependent eliminators can be used to define a monotone map
  -- function.

  module _ {a b} {A : Set a} {B : Set b} (f : A → B) where

    private

      map-args : Rec-args (λ (_ : A ⊥) → B ⊥) (λ u v _ → u ⊑ v)
      map-args = record
        { pe = never
        ; po = now ∘ f
        ; pl = λ _ → ⨆
        ; qr = λ _ → ⊑-refl
        ; qe = λ _ → never⊑
        ; qu = λ _ _ _ n pq pu pu-is-ub →
                 upper-bound′ pq pu pu-is-ub n
        ; ql = λ _ _ _ → least-upper-bound
        }

    map : A ⊥ → B ⊥
    map = ⊥-rec map-args

    map-monotone : ∀ {x y} → x ⊑ y → map x ⊑ map y
    map-monotone = ⊑-rec map-args

------------------------------------------------------------------------
-- The partiality monad
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Definition of _⊥ and _⊑_

-- The partiality monad (_⊥) and the information ordering (_⊑_) are
-- defined simultaneously.

infix 10 _⊥
infix  4 _⊑_ _⊒_

postulate
  _⊥  : ∀ {a} → Set a → Set a
  _⊑_ : ∀ {a} {A : Set a} → A ⊥ → A ⊥ → Set a

_⊒_ : ∀ {a} {A : Set a} → A ⊥ → A ⊥ → Set a
x ⊒ y = y ⊑ x

-- Increasing sequences.

Increasing-sequence : ∀ {a} → Set a → Set a
Increasing-sequence A = ∃ λ (f : ℕ → A ⊥) → ∀ n → f n ⊑ f (suc n)

module _ {a} {A : Set a} where

  -- Projection functions for Increasing-sequence.

  infix 30 _[_]

  _[_] : Increasing-sequence A → ℕ → A ⊥
  s [ n ] = proj₁ s n

  increasing : (s : Increasing-sequence A) →
               ∀ n → s [ n ] ⊑ s [ suc n ]
  increasing = proj₂

  -- Upper bounds.

  Is-upper-bound : Increasing-sequence A → A ⊥ → Set a
  Is-upper-bound s x = ∀ n → s [ n ] ⊑ x

  postulate
    -- _⊥ "constructors".
    never        : A ⊥
    now          : A → A ⊥
    ⨆            : Increasing-sequence A → A ⊥
    antisymmetry : {x y : A ⊥} → x ⊑ y → x ⊒ y → x ≡ y

    -- _⊑_ "constructors".
    ⊑-refl             : (x : A ⊥) → x ⊑ x
    never⊑             : (x : A ⊥) → never ⊑ x
    upper-bound′       : (s : Increasing-sequence A) (ub : A ⊥) →
                         ⨆ s ⊑ ub → Is-upper-bound s ub
    least-upper-bound  : (s : Increasing-sequence A) (ub : A ⊥) →
                         Is-upper-bound s ub → ⨆ s ⊑ ub
    ⊑-proof-irrelevant : {x y : A ⊥} → Proof-irrelevant (x ⊑ y)

  -- Predicate transformer related to increasing sequences.

  Inc : ∀ {p q}
        (P : A ⊥ → Set p)
        (Q : ∀ {x y} → P x → P y → x ⊑ y → Set q) →
        Increasing-sequence A → Set (p ⊔ q)
  Inc P Q s =
    ∃ λ (p : ∀ n → P (s [ n ])) →
      ∀ n → Q (p n) (p (suc n)) (increasing s n)

-- Dependent eliminators.
--
-- I (NAD) have tried to follow the spirit of the rules for HITs
-- specified in the HoTT-Agda library
-- (https://github.com/HoTT/HoTT-Agda/blob/master/lib/types/HIT_README.txt).
-- However, at the time of writing those rules don't apply to
-- indexed types.

-- Record wrapping up the eliminators' arguments.

record Rec-args
         {a p q} {A : Set a}
         (P : A ⊥ → Set p)
         (Q : ∀ {x y} → P x → P y → x ⊑ y → Set q) :
         Set (a ⊔ p ⊔ q) where
  field
    pe : P never
    po : ∀ x → P (now x)
    pl : ∀ s (pq : Inc P Q s) → P (⨆ s)
    pa : ∀ {x y} (x⊑y : x ⊑ y) (x⊒y : x ⊒ y)
         (p-x : P x) (p-y : P y)
         (q-x⊑y : Q p-x p-y x⊑y) (q-x⊒y : Q p-y p-x x⊒y) →
         subst P (antisymmetry x⊑y x⊒y) p-x ≡ p-y
    qr : ∀ x (p : P x) → Q p p (⊑-refl x)
    qe : ∀ x (p : P x) → Q pe p (never⊑ x)
    qu : ∀ s ub is-ub n (pq : Inc P Q s) (pu : P ub)
         (qu : Q (pl s pq) pu is-ub) →
         Q (proj₁ pq n) pu (upper-bound′ s ub is-ub n)
    ql : ∀ s ub is-ub (pq : Inc P Q s) (pu : P ub)
         (qu : ∀ n → Q (proj₁ pq n) pu (is-ub n)) →
         Q (pl s pq) pu (least-upper-bound s ub is-ub)
    qp : ∀ {x y} (p-x : P x) (p-y : P y) (x⊑y : x ⊑ y) →
         Proof-irrelevant (Q p-x p-y x⊑y)

-- The eliminators.

module _ {a p q} {A : Set a}
         {P : A ⊥ → Set p}
         {Q : ∀ {x y} → P x → P y → x ⊑ y → Set q}
         (args : Rec-args P Q) where

  open Rec-args args

  postulate
    ⊥-rec : (x : A ⊥) → P x
    ⊑-rec : ∀ {x y} (x⊑y : x ⊑ y) → Q (⊥-rec x) (⊥-rec y) x⊑y

  inc-rec : (s : Increasing-sequence A) → Inc P Q s
  inc-rec (s , inc) = ( (λ n → ⊥-rec (s   n))
                      , (λ n → ⊑-rec (inc n))
                      )

  -- Computation rules for _⊥.
  --
  -- NOTE: Rewriting has not been activated for the "computation" rule
  -- corresponding to antisymmetry.

  postulate

    ⊥-rec-never : ⊥-rec never ≡ pe
    ⊥-rec-now   : ∀ x → ⊥-rec (now x) ≡ po x
    ⊥-rec-⨆     : ∀ s → ⊥-rec (⨆ s) ≡ pl s (inc-rec s)
    ⊥-rec-antisymmetry :
      ∀ {x y} (x⊑y : x ⊑ y) (x⊒y : x ⊒ y) →
      dependent-cong ⊥-rec (antisymmetry x⊑y x⊒y) ≡
      pa x⊑y x⊒y (⊥-rec x) (⊥-rec y) (⊑-rec x⊑y) (⊑-rec x⊒y)

  {-# REWRITE ⊥-rec-never #-}
  {-# REWRITE ⊥-rec-now   #-}
  {-# REWRITE ⊥-rec-⨆     #-}

  -- Computation rules for _⊑_.
  --
  -- NOTE: There is no computation rule corresponding to
  -- ⊑-proof-irrelevant.

  postulate

    ⊑-rec-⊑-refl            : ∀ x → ⊑-rec (⊑-refl x) ≡ qr x (⊥-rec x)
    ⊑-rec-never⊑            : ∀ x → ⊑-rec (never⊑ x) ≡ qe x (⊥-rec x)
    ⊑-rec-upper-bound′      : ∀ s ub is-ub n →
                              ⊑-rec (upper-bound′ s ub is-ub n) ≡
                              qu s ub is-ub n
                                 (inc-rec s) (⊥-rec ub) (⊑-rec is-ub)
    ⊑-rec-least-upper-bound : ∀ s ub is-ub →
                              ⊑-rec (least-upper-bound s ub is-ub) ≡
                              ql s ub is-ub
                                 (inc-rec s)
                                 (⊥-rec ub)
                                 (λ n → ⊑-rec (is-ub n))

  {-# REWRITE ⊑-rec-⊑-refl            #-}
  {-# REWRITE ⊑-rec-never⊑            #-}
  {-# REWRITE ⊑-rec-upper-bound′      #-}
  {-# REWRITE ⊑-rec-least-upper-bound #-}

------------------------------------------------------------------------
-- Specialised eliminators

-- Non-dependent eliminators.

Inc-nd : ∀ {a p q}
         (A : Set a) (P : Set p)
         (Q : P → P → Set q) → Set (p ⊔ q)
Inc-nd A P Q = ∃ λ (p : ℕ → P) → ∀ n → Q (p n) (p (suc n))

record Rec-args-nd
         {a p q} (A : Set a) (P : Set p) (Q : P → P → Set q) :
         Set (a ⊔ p ⊔ q) where
  field
    pe : P
    po : (x : A) → P
    pl : (s : Increasing-sequence A) (pq : Inc-nd A P Q) → P
    pa : (p₁ p₂ : P) (q₁ : Q p₁ p₂) (q₂ : Q p₂ p₁) → p₁ ≡ p₂
    qr : (x : A ⊥) (p : P) → Q p p
    qe : (x : A ⊥) (p : P) → Q pe p
    qu : (s : Increasing-sequence A) (ub : A ⊥) (is-ub : ⨆ s ⊑ ub)
         (n : ℕ) (pq : Inc-nd A P Q) (pu : P)
         (qu : Q (pl s pq) pu) →
         Q (proj₁ pq n) pu
    ql : ∀ s (ub : A ⊥) (is-ub : Is-upper-bound s ub) pq (pu : P)
         (qu : ∀ n → Q (proj₁ pq n) pu) →
         Q (pl s pq) pu
    qp : (p₁ p₂ : P) → Is-proposition (Q p₁ p₂)

module _ {a p q} {A : Set a} {P : Set p} {Q : P → P → Set q}
         (args : Rec-args-nd A P Q) where

  open Rec-args-nd args

  private

    args′ : Rec-args {A = A} (λ _ → P) (λ p-x p-y _ → Q p-x p-y)
    args′ = record
      { pe = pe
      ; po = po
      ; pl = pl
      ; pa = λ x⊑y x⊒y p₁ p₂ q₁ q₂ →
               subst (const P) (antisymmetry x⊑y x⊒y) p₁  ≡⟨ subst-const (antisymmetry x⊑y x⊒y) ⟩
               p₁                                         ≡⟨ pa p₁ p₂ q₁ q₂ ⟩∎
               p₂                                         ∎
      ; qr = qr
      ; qe = qe
      ; qu = qu
      ; ql = ql
      ; qp = λ p-x p-y _ → _⇔_.to propositional⇔irrelevant (qp p-x p-y)
      }

  ⊥-rec-nd : A ⊥ → P
  ⊥-rec-nd = ⊥-rec args′

  ⊑-rec-nd : ∀ {x y} → x ⊑ y → Q (⊥-rec-nd x) (⊥-rec-nd y)
  ⊑-rec-nd = ⊑-rec args′

  inc-rec-nd : Increasing-sequence A → Inc-nd A P Q
  inc-rec-nd = inc-rec args′

-- An eliminator which is trivial for _⊑_.

record Rec-args-⊥ {a p} {A : Set a}
                  (P : A ⊥ → Set p) : Set (a ⊔ p) where
  field
    pe : P never
    po : ∀ x → P (now x)
    pl : ∀ s (p : ∀ n → P (s [ n ])) → P (⨆ s)
    pa : ∀ {x y} (x⊑y : x ⊑ y) (x⊒y : x ⊒ y)
         (p-x : P x) (p-y : P y) →
         subst P (antisymmetry x⊑y x⊒y) p-x ≡ p-y

module _ {a p} {A : Set a} {P : A ⊥ → Set p}
         (args : Rec-args-⊥ P) where

  open Rec-args-⊥ args

  ⊥-rec-⊥ : (x : A ⊥) → P x
  ⊥-rec-⊥ = ⊥-rec {Q = λ _ _ _ → ⊤} (record
    { pe = pe
    ; po = po
    ; pl = λ s pq → pl s (proj₁ pq)
    ; pa = λ x⊑y x⊒y p-x p-y _ _ → pa x⊑y x⊒y p-x p-y
    ; qp = λ _ _ _ _ _ → refl
    })

  inc-rec-⊥ : (s : ℕ → A ⊥) → ∀ n → P (s n)
  inc-rec-⊥ s = ⊥-rec-⊥ ∘ s

-- The previous eliminator can be simplified further if the motive is
-- propositional.

record Rec-args-Prop {a p} {A : Set a}
                     (P : A ⊥ → Set p) : Set (a ⊔ p) where
  field
    pe : P never
    po : ∀ x → P (now x)
    pl : ∀ s (p : ∀ n → P (s [ n ])) → P (⨆ s)
    pp : ∀ x → Is-proposition (P x)

module _ {a p} {A : Set a} {P : A ⊥ → Set p}
         (args : Rec-args-Prop P) where

  open Rec-args-Prop args

  ⊥-rec-Prop : (x : A ⊥) → P x
  ⊥-rec-Prop = ⊥-rec-⊥ (record
    { pe = pe
    ; po = po
    ; pl = pl
    ; pa = λ _ _ _ _ →
             _⇔_.to propositional⇔irrelevant (pp _) _ _
    })

  inc-rec-Prop : (s : ℕ → A ⊥) → ∀ n → P (s n)
  inc-rec-Prop s = ⊥-rec-Prop ∘ s

-- An eliminator which is trivial for _⊥.

record Rec-args-⊑ {a q} {A : Set a}
                  (Q : {x y : A ⊥} → x ⊑ y → Set q) :
                  Set (a ⊔ q) where
  field
    qr : ∀ x → Q (⊑-refl x)
    qe : ∀ x → Q (never⊑ x)
    qu : ∀ s ub is-ub n (q : ∀ n → Q (increasing s n)) (qu : Q is-ub) →
         Q (upper-bound′ s ub is-ub n)
    ql : ∀ s ub is-ub (q : ∀ n → Q (increasing s n))
         (qu : ∀ n → Q (is-ub n)) →
         Q (least-upper-bound s ub is-ub)
    qp : ∀ {x y} (x⊑y : x ⊑ y) →
         Is-proposition (Q x⊑y)

module _ {a q} {A : Set a} {Q : {x y : A ⊥} → x ⊑ y → Set q}
         (args : Rec-args-⊑ Q) where

  open Rec-args-⊑ args

  ⊑-rec-⊑ : ∀ {x y} (x⊑y : x ⊑ y) → Q x⊑y
  ⊑-rec-⊑ = ⊑-rec {P = λ _ → ⊤} {Q = λ _ _ → Q} (record
    { pa = λ _ _ _ _ _ _ → refl
    ; qr = λ x _ → qr x
    ; qe = λ x _ → qe x
    ; qu = λ s ub is-ub n pq _ → qu s ub is-ub n (proj₂ pq)
    ; ql = λ s ub is-ub pq _ → ql s ub is-ub (proj₂ pq)
    ; qp = λ _ _ → _⇔_.to propositional⇔irrelevant ∘ qp
    })

  inc-rec-⊑ : (s : Increasing-sequence A) → ∀ n → Q (increasing s n)
  inc-rec-⊑ (_ , inc) = ⊑-rec-⊑ ∘ inc

------------------------------------------------------------------------
-- Some simple definitions and properties

module _ {a} {A : Set a} where

  -- _⊑_ is propositional.

  ⊑-propositional : {x y : A ⊥} → Is-proposition (x ⊑ y)
  ⊑-propositional =
    _⇔_.from propositional⇔irrelevant ⊑-proof-irrelevant

  -- ⨆ s is an upper bound for the sequence s.

  upper-bound : (s : Increasing-sequence A) →
                Is-upper-bound s (⨆ s)
  upper-bound s = upper-bound′ s (⨆ s) (⊑-refl (⨆ s))

  -- _⊑_ is transitive.

  ⊑-trans : {x y z : A ⊥} → x ⊑ y → y ⊑ z → x ⊑ z
  ⊑-trans x⊑y = ⊑-rec-⊑ {Q = λ {x y} x⊑y → ∀ {z} → y ⊑ z → x ⊑ z}
    (record
       { qr = λ _ → id
       ; qe = λ _ _ → never⊑ _
       ; qu = λ s ub is-ub n q qu {z} ⨆s⊑z →
                q n (upper-bound′ s z (qu ⨆s⊑z) (suc n))
       ; ql = λ s ub _ _ qu {z} ub⊑z →
                least-upper-bound s z (λ n → qu n ub⊑z)
       ; qp = λ _ → implicit-Π-closure        ext 1 λ _ →
                    Π-closure {a = a} {b = a} ext 1 λ _ →
                    ⊑-propositional
       })
    x⊑y

  -- Preorder reasoning combinators.

  infix  -1 finally-⊑
  infix  -1 _■
  infixr -2 _⊑⟨_⟩_ _⊑⟨⟩_ _⊑⟨_⟩≡_

  _⊑⟨_⟩_ : (x {y z} : A ⊥) → x ⊑ y → y ⊑ z → x ⊑ z
  _ ⊑⟨ x⊑y ⟩ y⊑z = ⊑-trans x⊑y y⊑z

  _⊑⟨⟩_ : (x {y} : A ⊥) → x ⊑ y → x ⊑ y
  _ ⊑⟨⟩ x⊑y = x⊑y

  _⊑⟨_⟩≡_ : (x {y z} : A ⊥) → x ≡ y →
            y ⊑ z → x ⊑ z
  _ ⊑⟨ refl ⟩≡ y⊑z = y⊑z

  _■ : (x : A ⊥) → x ⊑ x
  x ■ = ⊑-refl x

  finally-⊑ : (x y : A ⊥) → x ⊑ y → x ⊑ y
  finally-⊑ _ _ x⊑y = x⊑y

  syntax finally-⊑ x y x⊑y = x ⊑⟨ x⊑y ⟩■ y ■

  -- ⨆ is monotone.

  ⨆-mono : {s₁ s₂ : Increasing-sequence A} →
           (∀ n → s₁ [ n ] ⊑ s₂ [ n ]) → ⨆ s₁ ⊑ ⨆ s₂
  ⨆-mono {s₁} {s₂} s₁⊑s₂ =
    least-upper-bound s₁ (⨆ s₂) (λ n →
      s₁ [ n ]  ⊑⟨ s₁⊑s₂ n ⟩
      s₂ [ n ]  ⊑⟨ upper-bound s₂ n ⟩■
      ⨆ s₂      ■)

  -- Later elements in an increasing sequence are larger.

  later-larger : (s : Increasing-sequence A) →
                 ∀ {m n} → m ≤ n → s [ m ] ⊑ s [ n ]
  later-larger s {m} ≤-refl             = s [ m ] ■
  later-larger s {m} (≤-step {n = n} p) =
    s [ m ]      ⊑⟨ later-larger s p ⟩
    s [ n ]      ⊑⟨ increasing s n ⟩■
    s [ suc n ]  ■

  private

    -- A lemma.

    ⊥-is-set-and-equality-characterisation : Is-set (A ⊥) × _
    ⊥-is-set-and-equality-characterisation =
      Eq.propositional-identity≃≡
        (λ x y → x ⊑ y × x ⊒ y)
        (λ _ _ → ×-closure 1 ⊑-propositional ⊑-propositional)
        (λ x → ⊑-refl x , ⊑-refl x)
        (λ x y → uncurry {B = λ _ → x ⊒ y} antisymmetry)

  -- _⊥ is a family of sets. (This lemma is analogous to
  -- Theorem 11.3.9 in "Homotopy Type Theory: Univalent Foundations of
  -- Mathematics" (first edition).)

  ⊥-is-set : Is-set (A ⊥)
  ⊥-is-set = proj₁ ⊥-is-set-and-equality-characterisation

  -- Equality characterisation lemma for the partiality monad.

  equality-characterisation-⊥ :
    {x y : A ⊥} → (x ⊑ y × x ⊒ y) ≃ (x ≡ y)
  equality-characterisation-⊥ =
    proj₂ ⊥-is-set-and-equality-characterisation ext

  -- Equality characterisation lemma for increasing sequences.

  equality-characterisation-increasing :
    {s₁ s₂ : Increasing-sequence A} →
    (∀ n → s₁ [ n ] ≡ s₂ [ n ]) ↔ s₁ ≡ s₂
  equality-characterisation-increasing {s₁} {s₂} =
    (∀ n → s₁ [ n ] ≡ s₂ [ n ])  ↔⟨ Eq.extensionality-isomorphism ext ⟩
    proj₁ s₁ ≡ proj₁ s₂          ↝⟨ ignore-propositional-component
                                      (Π-closure ext 1 λ _ →
                                       ⊑-propositional) ⟩□
    s₁ ≡ s₂                      □

  -- The tail of an increasing sequence.

  tailˢ : Increasing-sequence A → Increasing-sequence A
  tailˢ = Σ-map (_∘ suc) (_∘ suc)

  -- The tail has the same least upper bound as the full sequence.

  ⨆tail≡⨆ : ∀ s → ⨆ (tailˢ s) ≡ ⨆ s
  ⨆tail≡⨆ s = antisymmetry
    (least-upper-bound (tailˢ s) (⨆ s) (λ n →
       s [ suc n ]  ⊑⟨ upper-bound s (suc n) ⟩■
       ⨆ s          ■))
    (⨆-mono (λ n → s [ n ]      ⊑⟨ increasing s n ⟩■
                   s [ suc n ]  ■))

  -- Only never is smaller than or equal to never.

  only-never-⊑-never : {x : A ⊥} → x ⊑ never → x ≡ never
  only-never-⊑-never x⊑never = antisymmetry x⊑never (never⊑ _)

  -- The least value never is equal to the least upper bound of a
  -- constant sequence of nevers.

  never≡⨆never : never ≡ ⨆ ((λ _ → never {A = A}) , λ _ → never⊑ never)
  never≡⨆never =
    antisymmetry (never⊑ _) (least-upper-bound _ _ λ _ → never⊑ never)

  -- A termination predicate: x ⇓ y means that x terminates with the
  -- value y.

  infix 4 _⇓_

  _⇓_ : A ⊥ → A → Set a
  x ⇓ y = x ≡ now y

  -- An alternative characterisation of _⊑_.

  _≼_ : A ⊥ → A ⊥ → Set a
  x ≼ y = ∀ z → x ⇓ z → y ⇓ z

  -- _≼_ is propositional.

  ≼-propositional : ∀ {x y} → Is-proposition (x ≼ y)
  ≼-propositional =
    Π-closure ext 1 λ _ →
    Π-closure ext 1 λ _ →
    ⊥-is-set _ _

------------------------------------------------------------------------
-- Another alternative characterisation of _⊑_

-- This characterisation uses a technique from the first edition of
-- the HoTT book (Theorems 11.3.16 and 11.3.32).
--
-- The characterisation was developed together with Paolo Capriotti
-- and Nicolai Kraus.
--
-- The characterisation uses univalence.

module _ {a} {A : Set a} (univ : Univalence a) where

  -- A binary relation, defined using structural recursion.

  private

    now[_]≲-args : A → Rec-args-nd A (Proposition a)
                                   (λ P Q → proj₁ P → proj₁ Q)
    now[ x ]≲-args = record
      { pe = Prelude.⊥ , ⊥-propositional
      ; po = λ y → ∥ x ≡ y ∥ , truncation-is-proposition
      ; pl = λ { s (now-x≲s[_] , _) → ∥ ∃ (λ n → proj₁ (now-x≲s[ n ])) ∥
                                    , truncation-is-proposition
               }
      ; pa = λ now-x≲y now-x≲z now-x≲y→now-x≲z now-x≲z→now-x≲y →
                                              $⟨ record { to = now-x≲y→now-x≲z; from = now-x≲z→now-x≲y } ⟩
               proj₁ now-x≲y ⇔ proj₁ now-x≲z  ↝⟨ _↔_.to (⇔↔≡′ ext univ) ⟩□
               now-x≲y ≡ now-x≲z              □
      ; qr = λ { _ (now-x≲y , _) →
                 now-x≲y  ↝⟨ id ⟩□
                 now-x≲y  □
               }
      ; qe = λ { _ (now-x≲⊥ , _) →
                 Prelude.⊥  ↝⟨ ⊥-elim ⟩□
                 now-x≲⊥    □
               }
      ; qu = λ { _ _ _ n (now-x≲s[_] , _) (now-x≲ub , _)
                 now-x≲s[]→now-x≲ub →

                 proj₁ now-x≲s[ n ]                ↝⟨ ∣_∣ ∘ (n ,_) ⟩
                 ∥ ∃ (λ n → proj₁ now-x≲s[ n ]) ∥  ↝⟨ now-x≲s[]→now-x≲ub ⟩□
                 now-x≲ub                          □
               }
      ; ql = λ { s ub is-ub (now-x≲s[_] , _) now-x≲ub now-x≲s[]→now-x≲ub →
                 ∥ ∃ (λ n → proj₁ now-x≲s[ n ]) ∥  ↝⟨ Trunc.rec (proj₂ now-x≲ub) (uncurry now-x≲s[]→now-x≲ub) ⟩□
                 proj₁ now-x≲ub                    □
               }
      ; qp = λ _ now-x≲z → Π-closure ext 1 λ _ →
                           proj₂ now-x≲z
      }

    ≲-args : Rec-args-nd A (A ⊥ → Proposition a)
                         (λ P Q → ∀ z → proj₁ (Q z) → proj₁ (P z))
    ≲-args = record
      { pe = λ _ → ↑ _ ⊤ , ↑-closure 1 (mono₁ 0 ⊤-contractible)
      ; po = λ x y → ⊥-rec-nd now[ x ]≲-args y
      ; pl = λ { _ (s[_]≲ , _) y → (∀ n → proj₁ (s[ n ]≲ y))
                                 , Π-closure ext 1 λ n →
                                   proj₂ (s[ n ]≲ y)
               }
      ; pa = λ x≲ y≲ y≲→x≲ x≲→y≲ → ext λ z →
                                            $⟨ record { to = x≲→y≲ z; from = y≲→x≲ z } ⟩
               proj₁ (x≲ z) ⇔ proj₁ (y≲ z)  ↝⟨ _↔_.to (⇔↔≡′ ext univ) ⟩
               x≲ z ≡ y≲ z                  □
      ; qr = λ _ x≲ z →
               proj₁ (x≲ z)  ↝⟨ id ⟩□
               proj₁ (x≲ z)  □
      ; qe = λ _ ⊥≲ z →
               proj₁ (⊥≲ z)  ↝⟨ _ ⟩□
               ↑ _ ⊤         □
      ; qu = λ { _ _ _ n (s[_]≲ , _) ub≲ ub≲→s[]≲ z →
                 proj₁ (ub≲ z)      ↝⟨ flip (ub≲→s[]≲ z) n ⟩□
                 proj₁ (s[ n ]≲ z)  □
               }
      ; ql = λ { _ _ _ (s[_]≲ , _) ub≲ ub≲→s[]≲ z →
                 proj₁ (ub≲ z)              ↝⟨ flip (flip ub≲→s[]≲ z) ⟩□
                 (∀ n → proj₁ (s[ n ]≲ z))  □
               }
      ; qp = λ x≲ y≲ → Π-closure ext 1 λ z →
                       Π-closure ext 1 λ _ →
                       proj₂ (x≲ z)
      }

  infix 4 _≲_

  _≲_ : A ⊥ → A ⊥ → Set a
  x ≲ y = proj₁ (⊥-rec-nd ≲-args x y)

  -- The relation is propositional.

  ≲-propositional : ∀ x y → Is-proposition (x ≲ y)
  ≲-propositional x y = proj₂ (⊥-rec-nd ≲-args x y)

  -- A form of transitivity involving _⊑_ and _≲_.

  ⊑≲-trans : ∀ {x y} (z : A ⊥) → x ⊑ y → y ≲ z → x ≲ z
  ⊑≲-trans z x⊑y = ⊑-rec-nd ≲-args x⊑y z

  private

    -- Lemmas showing certain aspects of how _≲_ evaluates.

    never≲ : ∀ y → (never ≲ y) ≡ ↑ _ ⊤
    never≲ _ = refl

    ⨆≲ : ∀ s y → (⨆ s ≲ y) ≡ ∀ n → s [ n ] ≲ y
    ⨆≲ _ _ = refl

    now≲never : ∀ x → (now x ≲ never) ≡ Prelude.⊥
    now≲never _ = refl

    now≲now : ∀ x y → (now x ≲ now y) ≡ ∥ x ≡ y ∥
    now≲now _ _ = refl

    now≲⨆ : ∀ x s → (now x ≲ ⨆ s) ≡ ∥ (∃ λ n → now x ≲ s [ n ]) ∥
    now≲⨆ _ _ = refl

  -- _≲_ is reflexive.

  ≲-refl : ∀ x → x ≲ x
  ≲-refl = ⊥-rec-Prop (record
    { po = λ _ → ∣ refl ∣
    ; pl = λ s →
             (∀ n → s [ n ] ≲ s [ n ])  ↝⟨ (λ s≲s n → ⨆-lemma s (s [ n ]) n (s≲s n)) ⟩
             (∀ n → s [ n ] ≲ ⨆ s)      □
    ; pp = λ x → ≲-propositional x x
    })
    where
    ⨆-lemma : ∀ s x n → x ≲ s [ n ] → x ≲ ⨆ s
    ⨆-lemma s = ⊥-rec-Prop
      {P = λ x → ∀ n → x ≲ s [ n ] → x ≲ ⨆ s}
      (record
         { po = λ x n →
                  now x ≲ s [ n ]                ↝⟨ ∣_∣ ∘ (n ,_) ⟩
                  ∥ (∃ λ n → now x ≲ s [ n ]) ∥  □
         ; pl = λ s′ →
                  (∀ m n → s′ [ m ] ≲ s [ n ] → s′ [ m ] ≲ ⨆ s)  ↝⟨ (λ hyp n s′≲s m → hyp m n (s′≲s m)) ⟩
                  (∀ n → (∀ m → s′ [ m ] ≲ s [ n ]) →
                         (∀ m → s′ [ m ] ≲ ⨆ s))                 □
         ; pp = λ x → Π-closure ext 1 λ _ →
                      Π-closure ext 1 λ _ →
                      ≲-propositional x (⨆ s)
         })

  -- _⊑_ and _≲_ are pointwise equivalent.

  ⊑≃≲ : ∀ {x y} → (x ⊑ y) ≃ (x ≲ y)
  ⊑≃≲ {x} {y} =
    _↔_.to (Eq.⇔↔≃ ext ⊑-propositional (≲-propositional x y))
      (record { to   = ⊑-rec-⊑ to-args
              ; from = ⊥-rec-Prop from-args _ _
              })
    where
    to-args : Rec-args-⊑ (λ {x y} _ → x ≲ y)
    to-args = record
      { qr = λ x → ≲-refl x
      ; qu = λ s ub _ n _ ⨆s≲ub → ⨆s≲ub n
      ; ql = λ s ub _ _ s[_]≲ub n → s[ n ]≲ub
      ; qp = λ {x y} _ → ≲-propositional x y
      }

    now-lemma : ∀ x y → now x ≲ y → now x ⊑ y
    now-lemma x y = ⊥-rec-Prop
      {P = λ y → now x ≲ y → now x ⊑ y}
      (record
         { pe = Prelude.⊥      ↝⟨ ⊥-elim ⟩□
                now x ⊑ never  □
         ; po = λ y →
                  ∥ x ≡ y ∥        ↝⟨ Trunc.rec ⊑-propositional (

                    x ≡ y               ↝⟨ cong now ⟩
                    now x ≡ now y       ↝⟨ flip (subst (now x ⊑_)) (⊑-refl _) ⟩□
                    now x ⊑ now y       □) ⟩□

                  now x ⊑ now y    □
         ; pl = λ s now-x≲s→now-x⊑s →
                  ∥ ∃ (λ n → now x ≲ s [ n ]) ∥  ↝⟨ Trunc.rec ⊑-propositional (uncurry λ n now-x≲s[n] →

                    now x                             ⊑⟨ now-x≲s→now-x⊑s n now-x≲s[n] ⟩
                    s [ n ]                           ⊑⟨ upper-bound s n ⟩■
                    ⨆ s                               ■) ⟩□

                  now x ⊑ ⨆ s                    □
         ; pp = λ _ → Π-closure ext 1 λ _ →
                      ⊑-propositional
         })
      y

    from-args : Rec-args-Prop (λ x → ∀ y → x ≲ y → x ⊑ y)
    from-args = record
      { pe = λ y _ → never⊑ y
      ; po = now-lemma
      ; pl = λ s s≲→s⊑ y →
               (∀ n → s [ n ] ≲ y)  ↝⟨ (λ s[_]≲y n → s≲→s⊑ n y s[ n ]≲y) ⟩
               (∀ n → s [ n ] ⊑ y)  ↝⟨ least-upper-bound s y ⟩□
               ⨆ s ⊑ y              □
      ; pp = λ _ → Π-closure ext 1 λ _ →
                   Π-closure ext 1 λ _ →
                   ⊑-propositional
      }

------------------------------------------------------------------------
-- Some properties that follow from the equivalence between _⊑_ and
-- _≲_ (still assuming univalence)

  -- Defined values of the form now x are never smaller than or equal
  -- to never (assuming univalence).
  --
  -- This lemma was proved together with Paolo Capriotti and Nicolai
  -- Kraus.

  now⋢never : (x : A) → ¬ now x ⊑ never
  now⋢never x =
    now x ⊑ never  ↔⟨ ⊑≃≲ ⟩
    now x ≲ never  ↝⟨ ⊥-elim ⟩□
    ⊥₀             □

  -- Defined values of the form now x are never equal to never.

  now≢never : (x : A) → now x ≢ never
  now≢never x =
    now x ≡ never                  ↝⟨ _≃_.from equality-characterisation-⊥ ⟩
    now x ⊑ never × now x ⊒ never  ↝⟨ proj₁ ⟩
    now x ⊑ never                  ↝⟨ now⋢never x ⟩□
    ⊥₀                             □

  -- There is an equivalence between "now x is smaller than or equal
  -- to now y" and "x is merely equal to y".

  now⊑now≃∥≡∥ : {x y : A} → (now x ⊑ now y) ≃ ∥ x ≡ y ∥
  now⊑now≃∥≡∥ {x} {y} =
    now x ⊑ now y  ↝⟨ ⊑≃≲ ⟩
    now x ≲ now y  ↝⟨ F.id ⟩□
    ∥ x ≡ y ∥      □

  -- There is an equivalence between "now x is equal to now y" and "x
  -- is merely equal to y".

  now≡now≃∥≡∥ : {x y : A} → (now x ≡ now y) ≃ ∥ x ≡ y ∥
  now≡now≃∥≡∥ {x} {y} =
    now x ≡ now y                  ↝⟨ inverse equality-characterisation-⊥ ⟩
    now x ⊑ now y × now x ⊒ now y  ↝⟨ now⊑now≃∥≡∥ ×-cong now⊑now≃∥≡∥ ⟩
    ∥ x ≡ y ∥ × ∥ y ≡ x ∥          ↝⟨ _↔_.to (Eq.⇔↔≃ ext (×-closure 1 truncation-is-proposition
                                                                      truncation-is-proposition)
                                                         truncation-is-proposition)
                                             (record { to = proj₁
                                                     ; from = λ ∥x≡y∥ → ∥x≡y∥ , ∥∥-map sym ∥x≡y∥
                                                     }) ⟩□
    ∥ x ≡ y ∥                      □

  -- A computation can terminate with at most one value.

  termination-value-merely-unique :
    ∀ {x y z} → x ⇓ y → x ⇓ z → ∥ y ≡ z ∥
  termination-value-merely-unique {x} {y} {z} x⇓y x⇓z =
    _≃_.to now≡now≃∥≡∥ (
      now y  ≡⟨ sym x⇓y ⟩
      x      ≡⟨ x⇓z ⟩∎
      now z  ∎)

  -- If a computation terminates with a certain value, then all larger
  -- computations terminate with the same value.
  --
  -- Capretta proved a similar result in "General Recursion via
  -- Coinductive Types".

  larger-terminate-with-same-value : {x y : A ⊥} → x ⊑ y → x ≼ y
  larger-terminate-with-same-value = ⊑-rec-⊑
    {Q = λ {x y} _ → x ≼ y}
    (record
       { qr = λ x z →
                x ⇓ z  ↝⟨ id ⟩□
                x ⇓ z  □
       ; qe = λ x z →
                never ⇓ z  ↝⟨ now≢never z ∘ sym ⟩
                ⊥₀         ↝⟨ ⊥-elim ⟩□
                x ⇓ z      □
       ; qu = λ s ub _ n q qu x s[n]⇓x →                 $⟨ (λ _ n≤m → lemma s (flip q x) n≤m s[n]⇓x) ⟩
                (∀ m → n ≤ m → s [ m ] ≡ now x)          ↝⟨ (λ hyp m n≤m → proj₁ (_≃_.from equality-characterisation-⊥ (hyp m n≤m))) ⟩
                (∀ m → n ≤ m → s [ m ] ⊑ now x)          ↝⟨ (λ hyp m → [ (λ m≤n →

                  s [ m ]                                     ⊑⟨ later-larger s m≤n ⟩
                  s [ n ]                                     ⊑⟨ s[n]⇓x ⟩≡
                  now x                                       ■) , hyp m ]) ⟩

                (∀ m → m ≤ n ⊎ n ≤ m → s [ m ] ⊑ now x)  ↝⟨ (λ hyp m → hyp m (Nat.total m n)) ⟩
                (∀ m → s [ m ] ⊑ now x)                  ↝⟨ least-upper-bound s (now x) ⟩
                ⨆ s ⊑ now x                              ↝⟨ flip antisymmetry (

                  now x                                       ⊑⟨ sym s[n]⇓x ⟩≡
                  s [ n ]                                     ⊑⟨ upper-bound s n ⟩■
                  ⨆ s                                         ■) ⟩

                ⨆ s ⇓ x                                  ↝⟨ qu x ⟩□
                ub ⇓ x                                   □
       ; ql = λ s ub _ q qu x →
           ⨆ s ⇓ x                                                  ↔⟨ inverse equality-characterisation-⊥ ⟩
           ⨆ s ⊑ now x × ⨆ s ⊒ now x                                ↔⟨ ⊑≃≲ ×-cong ⊑≃≲ ⟩
           ⨆ s ≲ now x × now x ≲ ⨆ s                                ↝⟨ id ⟩
           (∀ n → s [ n ] ≲ now x) × ∥ ∃ (λ n → now x ≲ s [ n ]) ∥  ↝⟨ (uncurry λ all → ∥∥-map (Σ-map id (λ {n} →

             now x ≲ s [ n ]                                             ↝⟨ (λ now-x≲s[n] → now-x≲s[n] , all n) ⟩
             now x ≲ s [ n ] × s [ n ] ≲ now x                           ↔⟨ inverse (⊑≃≲ ×-cong ⊑≃≲) ⟩
             now x ⊑ s [ n ] × s [ n ] ⊑ now x                           ↔⟨ equality-characterisation-⊥ ⟩
             now x ≡ s [ n ]                                             ↝⟨ sym ⟩□
             s [ n ] ⇓ x                                                 □))) ⟩

           ∥ ∃ (λ n → s [ n ] ⇓ x) ∥                                ↝⟨ Trunc.rec (⊥-is-set _ _) (uncurry (flip qu x)) ⟩□
           ub ⇓ x                                                   □
       ; qp = λ _ → ≼-propositional
       })
    where
    lemma : ∀ s {x} →
            (∀ n → s [ n ] ⇓ x → s [ suc n ] ⇓ x) →
            ∀ {m n} → m ≤ n → s [ m ] ⇓ x → s [ n ] ⇓ x
    lemma s     hyp     ≤-refl             = id
    lemma s {x} hyp {m} (≤-step {n = n} p) =
      s [ m ]     ⇓ x  ↝⟨ lemma s hyp p ⟩
      s [ n ]     ⇓ x  ↝⟨ hyp n ⟩□
      s [ suc n ] ⇓ x  □

  -- If one element in an increasing sequence terminates with a given
  -- value, then this value is the sequence's least upper bound.

  terminating-element-is-⨆ :
    ∀ (s : Increasing-sequence A) {n x} →
    s [ n ] ⇓ x → ⨆ s ⇓ x
  terminating-element-is-⨆ s {n} {x} =
    larger-terminate-with-same-value (upper-bound s n) x

  -- The relation _≼_ is contained in _⊑_.
  --
  -- Capretta proved a similar result in "General Recursion via
  -- Coinductive Types".

  ≼→⊑ : {x y : A ⊥} → x ≼ y → x ⊑ y
  ≼→⊑ {x} {y} = ⊥-rec-Prop
    {P = λ x → x ≼ y → x ⊑ y}
    (record
       { pe = never ≼ y  ↝⟨ (λ _ → never⊑ y) ⟩
              never ⊑ y   □
       ; po = λ x →
                now x ≼ y              ↝⟨ (λ hyp → hyp x refl) ⟩
                y ⇓ x                  ↔⟨ inverse equality-characterisation-⊥ ⟩
                y ⊑ now x × y ⊒ now x  ↝⟨ proj₂ ⟩□
                now x ⊑ y              □
       ; pl = λ s s≼y→s⊑y →
                ⨆ s ≼ y                        ↝⟨ id ⟩
                (∀ z → ⨆ s ⇓ z → y ⇓ z)        ↝⟨ (λ hyp n z →

                  s [ n ] ⇓ z                       ↝⟨ larger-terminate-with-same-value (upper-bound s n) z ⟩
                  ⨆ s ⇓ z                           ↝⟨ hyp z ⟩□
                  y ⇓ z                             □) ⟩

                (∀ n z → s [ n ] ⇓ z → y ⇓ z)  ↝⟨ id ⟩
                (∀ n → s [ n ] ≼ y)            ↝⟨ (λ hyp n → s≼y→s⊑y n (hyp n)) ⟩
                (∀ n → s [ n ] ⊑ y)            ↝⟨ least-upper-bound s y ⟩□
                ⨆ s ⊑ y                        □
       ; pp = λ _ →
                Π-closure ext 1 λ _ →
                ⊑-propositional
       })
    x

  -- The two relations _≼_ and _⊑_ are pointwise equivalent.
  --
  -- Capretta proved a similar result in "General Recursion via
  -- Coinductive Types".

  ≼≃⊑ : {x y : A ⊥} → (x ≼ y) ≃ (x ⊑ y)
  ≼≃⊑ = _↔_.to (Eq.⇔↔≃ ext ≼-propositional ⊑-propositional)
               (record { to   = ≼→⊑
                       ; from = larger-terminate-with-same-value
                       })

  -- An alternative characterisation of _⇓_.

  ⇓≃now⊑ : ∀ {x} {y : A} → (x ⇓ y) ≃ (now y ⊑ x)
  ⇓≃now⊑ {x} {y} =
    _↔_.to (Eq.⇔↔≃ ext (⊥-is-set _ _) ⊑-propositional) (record
      { to   = x ≡ now y              ↔⟨ inverse equality-characterisation-⊥ ⟩
               x ⊑ now y × x ⊒ now y  ↝⟨ proj₂ ⟩□
               now y ⊑ x              □
      ; from = now y ⊑ x                  ↝⟨ larger-terminate-with-same-value ⟩
               (∀ z → now y ⇓ z → x ⇓ z)  ↝⟨ (λ hyp → hyp y refl) ⟩□
               x ⇓ y                      □
      })

  -- Another alternative characterisation of _⇓_.

  infix 4 _⇊_

  _⇊_ : A ⊥ → A → Set a
  x ⇊ y = now y ≲ x

  -- The relations _⇓_ and _⇊_ are pointwise equivalent.

  ⇓≃⇊ : ∀ {x y} → (x ⇓ y) ≃ (x ⇊ y)
  ⇓≃⇊ {x} {y} =
    x ⇓ y      ↝⟨ ⇓≃now⊑ ⟩
    now y ⊑ x  ↝⟨ ⊑≃≲ ⟩
    now y ≲ x  ↝⟨ F.id ⟩□
    x ⇊ y      □

------------------------------------------------------------------------
-- Monotone functions

-- Definition of monotone functions.

[_⊥→_⊥]⊑ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
[ A ⊥→ B ⊥]⊑ = ∃ λ (f : A ⊥ → B ⊥) → ∀ {x y} → x ⊑ y → f x ⊑ f y

-- Identity.

id⊑ : ∀ {a} {A : Set a} → [ A ⊥→ A ⊥]⊑
id⊑ = id , id

-- Composition.

infixr 40 _∘⊑_

_∘⊑_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
       [ B ⊥→ C ⊥]⊑ → [ A ⊥→ B ⊥]⊑ → [ A ⊥→ C ⊥]⊑
f ∘⊑ g = proj₁ f ∘ proj₁ g
       , proj₂ f ∘ proj₂ g

module _ {a b} {A : Set a} {B : Set b} where

  -- Equality characterisation lemma for monotone functions.

  equality-characterisation-monotone :
    ∀ {a b} {A : Set a} {B : Set b} {f g : [ A ⊥→ B ⊥]⊑} →
    (∀ x → proj₁ f x ≡ proj₁ g x) ↔ f ≡ g
  equality-characterisation-monotone {a} {f = f} {g} =
    (∀ x → proj₁ f x ≡ proj₁ g x)  ↔⟨ Eq.extensionality-isomorphism ext ⟩
    proj₁ f ≡ proj₁ g              ↝⟨ ignore-propositional-component
                                        (implicit-Π-closure ext 1 λ _ →
                                         implicit-Π-closure ext 1 λ _ →
                                         Π-closure          ext 1 λ _ →
                                         ⊑-propositional) ⟩□
    f ≡ g                          □

  -- If a monotone function is applied to an increasing sequence,
  -- then the result is another increasing sequence.

  [_$_]-inc :
    [ A ⊥→ B ⊥]⊑ → Increasing-sequence A → Increasing-sequence B
  [ f $ s ]-inc = (λ n → proj₁ f (s [ n ]))
                , (λ n → proj₂ f (increasing s n))

  -- A lemma relating monotone functions and least upper bounds.

  ⨆$⊑$⨆ : (f : [ A ⊥→ B ⊥]⊑) →
          ∀ s → ⨆ [ f $ s ]-inc ⊑ proj₁ f (⨆ s)
  ⨆$⊑$⨆ f s = least-upper-bound _ _ (λ n →

    [ f $ s ]-inc [ n ]  ⊑⟨ proj₂ f (

      s [ n ]                 ⊑⟨ upper-bound _ _ ⟩■
      ⨆ s                     ■) ⟩■

    proj₁ f (⨆ s)        ■)

------------------------------------------------------------------------
-- ω-continuous functions

-- Definition of ω-continuous functions.

[_⊥→_⊥] : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
[ A ⊥→ B ⊥] = ∃ λ (f : [ A ⊥→ B ⊥]⊑) →
                ∀ s → proj₁ f (⨆ s) ≡ ⨆ [ f $ s ]-inc

-- Identity.

idω : ∀ {a} {A : Set a} → [ A ⊥→ A ⊥]
idω = id⊑ , λ _ → refl

-- Composition.

infixr 40 _∘ω_

_∘ω_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
       [ B ⊥→ C ⊥] → [ A ⊥→ B ⊥] → [ A ⊥→ C ⊥]
f ∘ω g = proj₁ f ∘⊑ proj₁ g , λ s →
  proj₁ (proj₁ f) (proj₁ (proj₁ g) (⨆ s))  ≡⟨ cong (proj₁ (proj₁ f)) (proj₂ g s) ⟩
  proj₁ (proj₁ f) (⨆ [ proj₁ g $ s ]-inc)  ≡⟨ proj₂ f _ ⟩∎
  ⨆ [ proj₁ f ∘⊑ proj₁ g $ s ]-inc         ∎

-- Equality characterisation lemma for ω-continuous functions.

equality-characterisation-continuous :
  ∀ {a b} {A : Set a} {B : Set b} {f g : [ A ⊥→ B ⊥]} →
  (∀ x → proj₁ (proj₁ f) x ≡ proj₁ (proj₁ g) x) ↔ f ≡ g
equality-characterisation-continuous {a} {A = A} {B} {f} {g} =
  (∀ x → proj₁ (proj₁ f) x ≡ proj₁ (proj₁ g) x)  ↝⟨ equality-characterisation-monotone {A = A} {B = B} ⟩
  proj₁ f ≡ proj₁ g                              ↝⟨ ignore-propositional-component
                                                      (Π-closure ext 1 λ _ →
                                                       ⊥-is-set _ _) ⟩□
  f ≡ g                                          □

------------------------------------------------------------------------
-- The partiality monad's monad instance

-- Functions of type A → B ⊥ can be lifted to /ω-continuous/ functions
-- from A ⊥ to B ⊥.

module _ {a b} {A : Set a} {B : Set b} (f : A → B ⊥) where

  private

    =<<-args : Rec-args-nd A (B ⊥) _⊑_
    =<<-args = record
      { pe = never
      ; po = f
      ; pl = λ _ → ⨆
      ; pa = λ _ _ → antisymmetry
      ; qr = λ _ → ⊑-refl
      ; qe = λ _ → never⊑
      ; qu = λ _ _ _ n pq pu ⨆pq⊑pu →
               upper-bound′ pq pu ⨆pq⊑pu n
      ; ql = λ _ _ _ → least-upper-bound
      ; qp = λ _ _ → ⊑-propositional
      }

  infix 50 _∗ _∗-inc_

  _∗ : [ A ⊥→ B ⊥]
  _∗ = (⊥-rec-nd =<<-args , ⊑-rec-nd =<<-args) , λ _ → refl

  _∗-inc_ : Increasing-sequence A → Increasing-sequence B
  _∗-inc_ = inc-rec-nd =<<-args

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ : ∀ {a b} {A : Set a} {B : Set b} →
         A ⊥ → (A → B ⊥) → B ⊥
x >>=′ f = proj₁ (proj₁ (f ∗)) x

-- Instances of the monad laws with extra universe polymorphism.

module Monad-laws where

  left-identity : ∀ {a b} {A : Set a} {B : Set b} x (f : A → B ⊥) →
                  now x >>=′ f ≡ f x
  left-identity x f = refl

  right-identity : ∀ {a} {A : Set a} (x : A ⊥) →
                   x >>=′ now ≡ x
  right-identity = ⊥-rec-Prop
    (record
       { pe = refl
       ; po = λ _ → refl
       ; pl = λ s hyp →
                ⨆ s >>=′ now        ≡⟨⟩
                ⨆ (now ∗-inc s)     ≡⟨ cong ⨆ (_↔_.to equality-characterisation-increasing λ n →

                  s [ n ] >>=′ now       ≡⟨ hyp n ⟩∎
                  s [ n ]                ∎) ⟩∎

                ⨆ s                 ∎
       ; pp = λ _ → ⊥-is-set _ _
       })

  associativity : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
                  (x : A ⊥) (f : A → B ⊥) (g : B → C ⊥) →
                  x >>=′ (λ x → f x >>=′ g) ≡ x >>=′ f >>=′ g
  associativity x f g = ⊥-rec-Prop
    (record
       { pe = refl
       ; po = λ _ → refl
       ; pl = λ s hyp →
                ⨆ ((λ x → f x >>=′ g) ∗-inc s)     ≡⟨ cong ⨆ (_↔_.to equality-characterisation-increasing λ n →

                  s [ n ] >>=′ (λ x → f x >>=′ g)       ≡⟨ hyp n ⟩∎
                  s [ n ] >>=′ f >>=′ g                 ∎) ⟩∎

                ⨆ (g ∗-inc (f ∗-inc s))            ∎
       ; pp = λ _ → ⊥-is-set _ _
       })
    x

open Monad equality-with-J

instance

  -- The partiality monad's monad instance.

  partiality-monad : ∀ {ℓ} → Monad (_⊥ {a = ℓ})
  Raw-monad.return (Monad.raw-monad partiality-monad) = now
  Raw-monad._>>=_  (Monad.raw-monad partiality-monad) = _>>=′_
  Monad.left-identity  partiality-monad = Monad-laws.left-identity
  Monad.right-identity partiality-monad = Monad-laws.right-identity
  Monad.associativity  partiality-monad = Monad-laws.associativity

-- _⊥ is a functor.

map : ∀ {a b} {A : Set a} {B : Set b} →
      (A → B) → [ A ⊥→ B ⊥]
map f = (return ∘ f) ∗

map-id : ∀ {a} {A : Set a} →
         map (id {A = A}) ≡ idω
map-id =
  return ∗  ≡⟨ _↔_.to equality-characterisation-continuous (λ x →

    x >>= return  ≡⟨ right-identity x ⟩∎
    x             ∎) ⟩∎

  idω       ∎

map-∘ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
        (f : B → C) (g : A → B) →
        map (f ∘ g) ≡ map f ∘ω map g
map-∘ f g =
  (now ∘ f ∘ g) ∗                ≡⟨ _↔_.to equality-characterisation-continuous (λ x →

    x >>=′ (now ∘ f ∘ g)                     ≡⟨⟩
    x >>=′ (λ x → now (g x) >>=′ (now ∘ f))  ≡⟨ Monad-laws.associativity x (now ∘ g) (now ∘ f) ⟩∎
    x >>=′ (now ∘ g) >>=′ (now ∘ f)          ∎) ⟩∎

  (now ∘ f) ∗ ∘ω (now ∘ g) ∗  ∎

------------------------------------------------------------------------
-- Strict ω-continuous functions

-- Definition of strict ω-continuous functions.

[_⊥→_⊥]-strict : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
[ A ⊥→ B ⊥]-strict =
  ∃ λ (f : [ A ⊥→ B ⊥]) → proj₁ (proj₁ f) never ≡ never

-- Identity.

id-strict : ∀ {a} {A : Set a} → [ A ⊥→ A ⊥]-strict
id-strict = idω , refl

-- Composition.

infixr 40 _∘-strict_

_∘-strict_ :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
  [ B ⊥→ C ⊥]-strict → [ A ⊥→ B ⊥]-strict → [ A ⊥→ C ⊥]-strict
f ∘-strict g = proj₁ f ∘ω proj₁ g ,
  (proj₁ (proj₁ (proj₁ f)) (proj₁ (proj₁ (proj₁ g)) never)  ≡⟨ cong (proj₁ (proj₁ (proj₁ f))) (proj₂ g) ⟩
   proj₁ (proj₁ (proj₁ f)) never                            ≡⟨ proj₂ f ⟩∎
   never                                                    ∎)

-- Equality characterisation lemma for strict ω-continuous functions.

equality-characterisation-strict :
  ∀ {a b} {A : Set a} {B : Set b} {f g : [ A ⊥→ B ⊥]-strict} →
  (∀ x → proj₁ (proj₁ (proj₁ f)) x ≡ proj₁ (proj₁ (proj₁ g)) x) ↔ f ≡ g
equality-characterisation-strict {f = f} {g} =
  (∀ x → proj₁ (proj₁ (proj₁ f)) x ≡ proj₁ (proj₁ (proj₁ g)) x)  ↝⟨ equality-characterisation-continuous ⟩
  proj₁ f ≡ proj₁ g                                              ↝⟨ ignore-propositional-component (⊥-is-set _ _) ⟩□
  f ≡ g                                                          □

-- Strict ω-continuous functions satisfy an extra monad law.

>>=-∘-return :
  ∀ {a b} {A : Set a} {B : Set b} →
  (fs : [ A ⊥→ B ⊥]-strict) →
  let f = proj₁ (proj₁ (proj₁ fs)) in
  ∀ x → x >>=′ (f ∘ return) ≡ f x
>>=-∘-return fs = ⊥-rec-Prop
  {P = λ x → x >>=′ (f ∘ return) ≡ f x}
  (record
     { pe = never    ≡⟨ sym (proj₂ fs) ⟩∎
            f never  ∎
     ; po = λ _ → refl
     ; pl = λ s p →
              ⨆ s >>=′ (f ∘ return)     ≡⟨⟩
              ⨆ ((f ∘ return) ∗-inc s)  ≡⟨ cong ⨆ (_↔_.to equality-characterisation-increasing λ n →

                (f ∘ return) ∗-inc s [ n ]   ≡⟨ p n ⟩∎
                [ f⊑ $ s ]-inc [ n ]         ∎) ⟩

              ⨆ [ f⊑ $ s ]-inc          ≡⟨ sym $ proj₂ fω s ⟩∎
              f (⨆ s)                   ∎
     ; pp = λ _ → ⊥-is-set _ _
     })
  where
  fω = proj₁ fs
  f⊑ = proj₁ fω
  f  = proj₁ f⊑

-- Strict ω-continuous functions from A ⊥ to B ⊥ are isomorphic to
-- functions from A to B ⊥.

partial↔strict :
  ∀ {a b} {A : Set a} {B : Set b} →
  (A → B ⊥) ↔ [ A ⊥→ B ⊥]-strict
partial↔strict {a} = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f → f ∗ , refl
      ; from = λ f x → proj₁ (proj₁ (proj₁ f)) (return x)
      }
    ; right-inverse-of    = λ fs →
        let f = proj₁ (proj₁ (proj₁ fs)) in
        _↔_.to equality-characterisation-strict λ x →
          x >>=′ (f ∘ return)  ≡⟨ >>=-∘-return fs x ⟩∎
          f x                  ∎
    }
  ; left-inverse-of = λ f → ext λ x →
      return x >>=′ f  ≡⟨ Monad-laws.left-identity x f ⟩∎
      f x              ∎
  }

------------------------------------------------------------------------
-- A fixpoint combinator

module _ {a} {A : Set a} where

  -- Repeated composition of a monotone function with itself.

  comp : [ A ⊥→ A ⊥]⊑ → ℕ → [ A ⊥→ A ⊥]⊑
  comp f zero    = id⊑
  comp f (suc n) = comp f n ∘⊑ f

  -- Pre-composition with the function is pointwise equal to
  -- post-composition with the function.

  pre≡post : ∀ f n {x} →
             proj₁ (comp f n ∘⊑ f) x ≡ proj₁ (f ∘⊑ comp f n) x
  pre≡post f zero        = refl
  pre≡post f (suc n) {x} =
    proj₁ (comp f n ∘⊑ f) (proj₁ f x)  ≡⟨ pre≡post f n ⟩∎
    proj₁ (f ∘⊑ comp f n) (proj₁ f x)  ∎

  -- An increasing sequence consisting of repeated applications of the
  -- given monotone function to never.

  fix-sequence : [ A ⊥→ A ⊥]⊑ → Increasing-sequence A
  fix-sequence f =
      (λ n → proj₁ (comp f n) never)
    , (λ n →
         proj₁ (comp f n) never            ⊑⟨ proj₂ (comp f n) (never⊑ (proj₁ f never)) ⟩■
         proj₁ (comp f n) (proj₁ f never)  ■)

  -- Taking the tail of this sequence amounts to the same thing as
  -- applying the function to each element in the sequence.

  tailˢ-fix-sequence :
    (f : [ A ⊥→ A ⊥]⊑) →
    tailˢ (fix-sequence f) ≡ [ f $ fix-sequence f ]-inc
  tailˢ-fix-sequence f =
    _↔_.to equality-characterisation-increasing λ n →
      proj₁ (comp f n ∘⊑ f) never  ≡⟨ pre≡post f n ⟩∎
      proj₁ (f ∘⊑ comp f n) never  ∎

  -- The sequence has the same least upper bound as the sequence you
  -- get if you apply the function to each element of the sequence.

  ⨆-fix-sequence :
    (f : [ A ⊥→ A ⊥]⊑) →
    ⨆ (fix-sequence f) ≡ ⨆ [ f $ fix-sequence f ]-inc
  ⨆-fix-sequence f =
    ⨆ (fix-sequence f)            ≡⟨ sym $ ⨆tail≡⨆ _ ⟩
    ⨆ (tailˢ (fix-sequence f))    ≡⟨ cong ⨆ (tailˢ-fix-sequence f) ⟩∎
    ⨆ [ f $ fix-sequence f ]-inc  ∎

  -- A fixpoint combinator.

  fix : [ A ⊥→ A ⊥]⊑ → A ⊥
  fix f = ⨆ (fix-sequence f)

  -- The fixpoint combinator produces fixpoints for ω-continuous
  -- arguments.

  fix-is-fixpoint-combinator :
    (fω : [ A ⊥→ A ⊥]) →
    let f⊑ : [ A ⊥→ A ⊥]⊑
        f⊑ = proj₁ fω

        f : A ⊥ → A ⊥
        f = proj₁ f⊑
    in fix f⊑ ≡ f (fix f⊑)
  fix-is-fixpoint-combinator fω =
    fix f⊑                          ≡⟨⟩
    ⨆ (fix-sequence f⊑)             ≡⟨ ⨆-fix-sequence f⊑ ⟩
    ⨆ [ f⊑ $ fix-sequence f⊑ ]-inc  ≡⟨ sym $ proj₂ fω _ ⟩
    f (⨆ (fix-sequence f⊑))         ≡⟨ refl ⟩∎
    f (fix f⊑)                      ∎
    where
    f⊑ : [ A ⊥→ A ⊥]⊑
    f⊑ = proj₁ fω

    f : A ⊥ → A ⊥
    f = proj₁ f⊑

  -- A variant of fix.

  fix′ : (A → A ⊥) → A ⊥
  fix′ f = fix (proj₁ (f ∗))

  -- This variant also produces a kind of fixpoint.

  fix′-is-fixpoint-combinator :
    (f : A → A ⊥) →
    fix′ f ≡ fix′ f >>= f
  fix′-is-fixpoint-combinator f =
    fix′ f                   ≡⟨⟩
    fix (proj₁ (f ∗))        ≡⟨ fix-is-fixpoint-combinator (f ∗) ⟩∎
    fix (proj₁ (f ∗)) >>= f  ∎

------------------------------------------------------------------------
-- Another fixpoint combinator

-- TODO: Is it possible to find some suitable abstraction and have
-- only one implementation of a fixpoint combinator?

-- Partial function transformers.

Trans : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Trans A B = (A → B ⊥) → (A → B ⊥)

-- Monotone partial function transformers.

Trans-⊑ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Trans-⊑ A B = ∃ λ (f : (A → B ⊥) → (A → B ⊥)) →
            ∀ {g₁ g₂} → (∀ x → g₁ x ⊑ g₂ x) → ∀ x → f g₁ x ⊑ f g₂ x

-- Monotone partial function transformers can be turned into
-- parametrised increasing sequence transformers.

[_$_at_]-inc :
  ∀ {a b} {A : Set a} {B : Set b} →
  Trans-⊑ A B →
  (A → Increasing-sequence B) → (A → Increasing-sequence B)
[ f $ s at x ]-inc =
    (λ n → proj₁ f (λ x → s x [ n ]) x)
  , (λ n → proj₂ f (λ x → increasing (s x) n) x)

-- Partial function transformers that are ω-continuous.

Trans-ω : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Trans-ω A B = ∃ λ (f : Trans-⊑ A B) →
                (s : A → Increasing-sequence B) (x : A) →
                proj₁ f (⨆ ∘ s) x ≡ ⨆ [ f $ s at x ]-inc

module _ {a b} {A : Set a} {B : Set b} where

  -- Repeated application of a partial function transformer to never.

  app : Trans A B → ℕ → (A → B ⊥)
  app f zero    = const never
  app f (suc n) = f (app f n)

  -- An increasing sequence consisting of repeated applications of the
  -- given partial function transformer to never.

  fix→-sequence : (f : Trans-⊑ A B) → A → Increasing-sequence B
  fix→-sequence f x =
      (λ n → app (proj₁ f) n x)
    , (λ n →
         app (proj₁ f) n       x  ⊑⟨ app-increasing n x ⟩■
         app (proj₁ f) (suc n) x  ■)
    where
    app-increasing :
      ∀ n x → app (proj₁ f) n x ⊑ app (proj₁ f) (suc n) x
    app-increasing zero    = never⊑ ∘ proj₁ f (const never)
    app-increasing (suc n) = proj₂ f (app-increasing n)

  -- A fixpoint combinator.

  fix→ : Trans-⊑ A B → (A → B ⊥)
  fix→ f x = ⨆ (fix→-sequence f x)

  -- The fixpoint combinator produces fixpoints for ω-continuous
  -- arguments.

  fix→-is-fixpoint-combinator :
    (fω : Trans-ω A B) →
    let f⊑ : Trans-⊑ A B
        f⊑ = proj₁ fω

        f : Trans A B
        f = proj₁ f⊑
    in
    fix→ f⊑ ≡ f (fix→ f⊑)
  fix→-is-fixpoint-combinator (f , ω-cont) = ext λ x →
    fix→ f x                            ≡⟨⟩
    ⨆ (fix→-sequence f x)               ≡⟨ sym $ ⨆tail≡⨆ _ ⟩
    ⨆ (tailˢ (fix→-sequence f x))       ≡⟨ cong ⨆ (_↔_.to equality-characterisation-increasing (λ _ → refl)) ⟩
    ⨆ [ f $ fix→-sequence f at x ]-inc  ≡⟨ sym $ ω-cont (fix→-sequence f) x ⟩
    proj₁ f (⨆ ∘ fix→-sequence f) x     ≡⟨ refl ⟩∎
    proj₁ f (fix→ f) x                  ∎
