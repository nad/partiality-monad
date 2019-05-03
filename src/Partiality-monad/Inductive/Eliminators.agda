------------------------------------------------------------------------
-- Specialised eliminators
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Partiality-monad.Inductive.Eliminators where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (⊥)

open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Nat equality-with-J as Nat

open import Partiality-monad.Inductive

------------------------------------------------------------------------
-- Non-dependent eliminators

Inc-nd : ∀ {a p q}
         (A : Set a) (P : Set p)
         (Q : P → P → Set q) → Set (p ⊔ q)
Inc-nd A P Q = ∃ λ (p : ℕ → P) → ∀ n → Q (p n) (p (suc n))

record Arguments-nd {a} p q (A : Set a) : Set (a ⊔ lsuc (p ⊔ q)) where
  field
    P  : Set p
    Q  : P → P → Set q
    pe : P
    po : (x : A) → P
    pl : (s : Increasing-sequence A) (pq : Inc-nd A P Q) → P
    pa : (p₁ p₂ : P) (q₁ : Q p₁ p₂) (q₂ : Q p₂ p₁) → p₁ ≡ p₂
    ps : Is-set P
    qr : (x : A ⊥) (p : P) → Q p p
    qt : {x y z : A ⊥} → x ⊑ y → y ⊑ z →
         (px py pz : P) → Q px py → Q py pz → Q px pz
    qe : (x : A ⊥) (p : P) → Q pe p
    qu : (s : Increasing-sequence A) (pq : Inc-nd A P Q) (n : ℕ) →
         Q (proj₁ pq n) (pl s pq)
    ql : ∀ s (ub : A ⊥) (is-ub : Is-upper-bound s ub) pq (pu : P)
         (qu : ∀ n → Q (proj₁ pq n) pu) →
         Q (pl s pq) pu
    qp : (p₁ p₂ : P) → Is-proposition (Q p₁ p₂)

module _ {a p q} {A : Set a} (args : Arguments-nd p q A) where

  open Arguments-nd args

  private

    args′ : Arguments p q A
    args′ = record
      { P  = λ _ → P
      ; Q  = λ p-x p-y _ → Q p-x p-y
      ; pe = pe
      ; po = po
      ; pl = pl
      ; pa = λ x⊑y x⊒y p₁ p₂ q₁ q₂ →
               subst (const P) (antisymmetry x⊑y x⊒y) p₁  ≡⟨ subst-const (antisymmetry x⊑y x⊒y) ⟩
               p₁                                         ≡⟨ pa p₁ p₂ q₁ q₂ ⟩∎
               p₂                                         ∎
      ; pp = _⇔_.to set⇔UIP ps
      ; qr = qr
      ; qt = qt
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

  ⊥-rec-nd-never : ⊥-rec-nd never ≡ pe
  ⊥-rec-nd-never = ⊥-rec-never _

  ⊥-rec-nd-now : ∀ x → ⊥-rec-nd (now x) ≡ po x
  ⊥-rec-nd-now = ⊥-rec-now _

  ⊥-rec-nd-⨆ : ∀ s → ⊥-rec-nd (⨆ s) ≡ pl s (inc-rec-nd s)
  ⊥-rec-nd-⨆ = ⊥-rec-⨆ _

------------------------------------------------------------------------
-- Eliminators which are trivial for _⊑_

record Arguments-⊥ {a} p (A : Set a) : Set (a ⊔ lsuc p) where
  field
    P  : A ⊥ → Set p
    pe : P never
    po : ∀ x → P (now x)
    pl : ∀ s (p : ∀ n → P (s [ n ])) → P (⨆ s)
    pp : ∀ x → Is-proposition (P x)

module _ {a p} {A : Set a} (args : Arguments-⊥ p A) where

  open Arguments-⊥ args

  ⊥-rec-⊥ : (x : A ⊥) → P x
  ⊥-rec-⊥ = ⊥-rec (record
    { Q  = λ _ _ _ → ⊤
    ; pe = pe
    ; po = po
    ; pl = λ s pq → pl s (proj₁ pq)
    ; pa = λ _ _ _ _ _ _ →
             _⇔_.to propositional⇔irrelevant (pp _) _ _
    ; pp = _⇔_.to propositional⇔irrelevant (mono₁ 1 (pp _) _ _)
    ; qp = λ _ _ _ _ _ → refl
    })

  inc-rec-⊥ : (s : ℕ → A ⊥) → ∀ n → P (s n)
  inc-rec-⊥ s = ⊥-rec-⊥ ∘ s

  ⊥-rec-⊥-never : ⊥-rec-⊥ never ≡ pe
  ⊥-rec-⊥-never = ⊥-rec-never _

  ⊥-rec-⊥-now : ∀ x → ⊥-rec-⊥ (now x) ≡ po x
  ⊥-rec-⊥-now = ⊥-rec-now _

  ⊥-rec-⊥-⨆ : ∀ s → ⊥-rec-⊥ (⨆ s) ≡ pl s (λ n → ⊥-rec-⊥ (s [ n ]))
  ⊥-rec-⊥-⨆ = ⊥-rec-⨆ _

------------------------------------------------------------------------
-- Eliminators which are trivial for _⊥

record Arguments-⊑ {a} q (A : Set a) : Set (a ⊔ lsuc q) where
  field
    Q  : {x y : A ⊥} → x ⊑ y → Set q
    qr : ∀ x → Q (⊑-refl x)
    qt : ∀ {x y z} (x⊑y : x ⊑ y) (y⊑z : y ⊑ z) →
         Q x⊑y → Q y⊑z → Q (⊑-trans x⊑y y⊑z)
    qe : ∀ x → Q (never⊑ x)
    qu : ∀ s (q : ∀ n → Q (increasing s n)) n →
         Q (upper-bound s n)
    ql : ∀ s ub is-ub (q : ∀ n → Q (increasing s n))
         (qu : ∀ n → Q (is-ub n)) →
         Q (least-upper-bound s ub is-ub)
    qp : ∀ {x y} (x⊑y : x ⊑ y) →
         Is-proposition (Q x⊑y)

module _ {a q} {A : Set a} (args : Arguments-⊑ q A) where

  open Arguments-⊑ args

  ⊑-rec-⊑ : ∀ {x y} (x⊑y : x ⊑ y) → Q x⊑y
  ⊑-rec-⊑ = ⊑-rec (record
    { P  = λ _ → ⊤
    ; Q  = λ _ _ → Q
    ; pa = λ _ _ _ _ _ _ → refl
    ; pp = _⇔_.to propositional⇔irrelevant
             (mono (Nat.zero≤ 2) ⊤-contractible _ _)
    ; qr = λ x _ → qr x
    ; qt = λ x⊑y y⊑z _ _ _ → qt x⊑y y⊑z
    ; qe = λ x _ → qe x
    ; qu = λ s pq → qu s (proj₂ pq)
    ; ql = λ s ub is-ub pq _ → ql s ub is-ub (proj₂ pq)
    ; qp = λ _ _ → _⇔_.to propositional⇔irrelevant ∘ qp
    })

  inc-rec-⊑ : (s : Increasing-sequence A) → ∀ n → Q (increasing s n)
  inc-rec-⊑ (_ , inc) = ⊑-rec-⊑ ∘ inc
