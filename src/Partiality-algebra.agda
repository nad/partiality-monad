------------------------------------------------------------------------
-- Partiality algebras
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Partiality-algebra where

open import Equality.Propositional
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (id) renaming (_∘_ to _⊚_)

open import Bijection equality-with-J as Bijection using (_↔_)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J as H-level hiding (Type)
open import H-level.Closure equality-with-J
open import Univalence-axiom equality-with-J

------------------------------------------------------------------------
-- Partiality algebras

-- Partiality algebras for certain universe levels and types, with a
-- certain underlying type.

record Partiality-algebra-with
  {a p} (Type : Set p) q (A : Set a) : Set (a ⊔ p ⊔ lsuc q) where

  -- A binary relation on the type.

  infix 4 _⊑_ _⊒_

  field
    _⊑_ : Type → Type → Set q

  _⊒_ : Type → Type → Set q
  _⊒_ x y = y ⊑ x

  -- Increasing sequences.

  Increasing-sequence : Set (p ⊔ q)
  Increasing-sequence = ∃ λ (f : ℕ → Type) → ∀ n → f n ⊑ f (suc n)

  -- Projection functions for Increasing-sequence.

  infix 30 _[_]

  _[_] : Increasing-sequence → ℕ → Type
  _[_] s n = proj₁ s n

  increasing : (s : Increasing-sequence) →
               ∀ n → (s [ n ]) ⊑ (s [ suc n ])
  increasing = proj₂

  -- Upper bounds.

  Is-upper-bound : Increasing-sequence → Type → Set q
  Is-upper-bound s x = ∀ n → (s [ n ]) ⊑ x

  field
    -- Type "constructors".

    never        : Type
    now          : A → Type
    ⨆            : Increasing-sequence → Type
    antisymmetry : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y

    -- We have chosen to explicitly make the type set-truncated.
    -- However, this "constructor" is not used anywhere in the
    -- development.
    Type-UIP-unused : Uniqueness-of-identity-proofs Type

    -- _⊑_ "constructors".

    ⊑-refl             : ∀ x → x ⊑ x
    ⊑-trans            : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
    never⊑             : ∀ x → never ⊑ x
    upper-bound        : ∀ s → Is-upper-bound s (⨆ s)
    least-upper-bound  : ∀ s ub → Is-upper-bound s ub → ⨆ s ⊑ ub
    ⊑-proof-irrelevant : ∀ {x y} → Proof-irrelevant (x ⊑ y)

  ----------------------------------------------------------------------
  -- Some simple consequences

  -- _⊑_ is propositional.

  ⊑-propositional : ∀ {x y} → Is-proposition (x ⊑ y)
  ⊑-propositional =
    _⇔_.from propositional⇔irrelevant ⊑-proof-irrelevant

  private

    -- A lemma.

    Type-is-set-and-equality-characterisation : Is-set Type × _
    Type-is-set-and-equality-characterisation =
      Eq.propositional-identity≃≡
        (λ x y → x ⊑ y × y ⊑ x)
        (λ _ _ → ×-closure 1 ⊑-propositional ⊑-propositional)
        (λ x → ⊑-refl x , ⊑-refl x)
        (λ x y → uncurry {B = λ _ → y ⊑ x} antisymmetry)

  -- Type is a set. (This lemma is analogous to Theorem 11.3.9 in
  -- "Homotopy Type Theory: Univalent Foundations of Mathematics"
  -- (first edition).)

  Type-is-set : Is-set Type
  Type-is-set = proj₁ Type-is-set-and-equality-characterisation

  -- Equality characterisation lemma for Type.

  equality-characterisation-Type :
    ∀ {x y} → (x ⊑ y × y ⊑ x) ≃ (x ≡ y)
  equality-characterisation-Type =
    proj₂ Type-is-set-and-equality-characterisation ext

  -- Equality characterisation lemma for increasing sequences.

  equality-characterisation-increasing :
    ∀ {s₁ s₂} → (∀ n → s₁ [ n ] ≡ s₂ [ n ]) ↔ s₁ ≡ s₂
  equality-characterisation-increasing {s₁} {s₂} =
    (∀ n → s₁ [ n ] ≡ s₂ [ n ])  ↔⟨ Eq.extensionality-isomorphism ext ⟩
    proj₁ s₁ ≡ proj₁ s₂          ↝⟨ ignore-propositional-component
                                      (Π-closure ext 1 λ _ →
                                       ⊑-propositional) ⟩□
    s₁ ≡ s₂                      □

-- Partiality algebras for certain universe levels and types.

record Partiality-algebra {a} p q (A : Set a) :
                          Set (a ⊔ lsuc (p ⊔ q)) where
  constructor ⟨_⟩
  field
    -- A type.

    {Type} : Set p

    -- A partiality-algebra with that type as the underlying type.

    partiality-algebra-with : Partiality-algebra-with Type q A

  open Partiality-algebra-with partiality-algebra-with public

------------------------------------------------------------------------
-- Partiality algebra morphisms

-- Morphisms from one partiality algebra to another.

record Morphism {a p₁ p₂ q₁ q₂} {A : Set a}
                (P₁ : Partiality-algebra p₁ q₁ A)
                (P₂ : Partiality-algebra p₂ q₂ A) :
                Set (a ⊔ p₁ ⊔ p₂ ⊔ q₁ ⊔ q₂) where

  private
    module P₁ = Partiality-algebra P₁
    module P₂ = Partiality-algebra P₂

  field
    function : P₁.Type → P₂.Type
    monotone : ∀ {x y} → x P₁.⊑ y → function x P₂.⊑ function y

  sequence-function : P₁.Increasing-sequence → P₂.Increasing-sequence
  sequence-function = Σ-map (function ⊚_) (monotone ⊚_)

  field
    strict       : function P₁.never ≡ P₂.never
    now-to-now   : ∀ x → function (P₁.now x) ≡ P₂.now x
    ω-continuous : ∀ s → function (P₁.⨆ s) ≡ P₂.⨆ (sequence-function s)

-- An identity morphism.

id : ∀ {a p q} {A : Set a} {P : Partiality-algebra p q A} → Morphism P P
id = record
  { function     = Prelude.id
  ; monotone     = Prelude.id
  ; strict       = refl
  ; now-to-now   = λ _ → refl
  ; ω-continuous = λ _ → refl
  }

-- Composition of morphisms.

_∘_ : ∀ {a p₁ p₂ p₃ q₁ q₂ q₃} {A : Set a}
        {P₁ : Partiality-algebra p₁ q₁ A}
        {P₂ : Partiality-algebra p₂ q₂ A}
        {P₃ : Partiality-algebra p₃ q₃ A} →
      Morphism P₂ P₃ → Morphism P₁ P₂ → Morphism P₁ P₃
_∘_ {P₁ = P₁} {P₂} {P₃} m₁ m₂ = record
  { function     = function m₁ ⊚ function m₂
  ; monotone     = monotone m₁ ⊚ monotone m₂
  ; strict       = function m₁ (function m₂ (never P₁))  ≡⟨ cong (function m₁) (strict m₂) ⟩
                   function m₁ (never P₂)                ≡⟨ strict m₁ ⟩∎
                   never P₃                              ∎
  ; now-to-now   = λ x →
                     function m₁ (function m₂ (now P₁ x))  ≡⟨ cong (function m₁) (now-to-now m₂ x) ⟩
                     function m₁ (now P₂ x)                ≡⟨ now-to-now m₁ x ⟩∎
                     now P₃ x                              ∎
  ; ω-continuous = λ s →
      function m₁ (function m₂ (⨆ P₁ s))                    ≡⟨ cong (function m₁) (ω-continuous m₂ s) ⟩
      function m₁ (⨆ P₂ (sequence-function m₂ s))           ≡⟨ ω-continuous m₁ (sequence-function m₂ s) ⟩∎
      ⨆ P₃ (sequence-function m₁ (sequence-function m₂ s))  ∎
  }
  where
  open Morphism
  open Partiality-algebra

-- Is-morphism-with P Q f holds if f is a morphism from P to Q.

Is-morphism-with :
  ∀ {a p₁ p₂ q₁ q₂} {Type₁ : Set p₁} {Type₂ : Set p₂} {A : Set a}
  (P₁ : Partiality-algebra-with Type₁ q₁ A)
  (P₂ : Partiality-algebra-with Type₂ q₂ A) →
  (Type₁ → Type₂) → Set _
Is-morphism-with P₁ P₂ f =
  ∃ λ (m : ∀ {x y} → x P₁.⊑ y → f x P₂.⊑ f y) →
  f P₁.never ≡ P₂.never
    ×
  (∀ x → f (P₁.now x) ≡ P₂.now x)
    ×
  (∀ s → f (P₁.⨆ s) ≡ P₂.⨆ (Σ-map (f ⊚_) (m ⊚_) s))
  where
  module P₁ = Partiality-algebra-with P₁
  module P₂ = Partiality-algebra-with P₂

-- Is-morphism P Q f holds if f is a morphism from P to Q.

Is-morphism :
  let open Partiality-algebra in
  ∀ {a p₁ p₂ q₁ q₂} {A : Set a}
  (P₁ : Partiality-algebra p₁ q₁ A) (P₂ : Partiality-algebra p₂ q₂ A) →
  (Type P₁ → Type P₂) → Set _
Is-morphism P₁ P₂ =
  Is-morphism-with P₁.partiality-algebra-with
                   P₂.partiality-algebra-with
  where
  module P₁ = Partiality-algebra P₁
  module P₂ = Partiality-algebra P₂

-- An alternative definition of morphisms.

Morphism-as-Σ :
  ∀ {a p₁ p₂ q₁ q₂} {A : Set a} →
  Partiality-algebra p₁ q₁ A → Partiality-algebra p₂ q₂ A → Set _
Morphism-as-Σ P₁ P₂ =
  ∃ λ (f : P₁.Type → P₂.Type) → Is-morphism P₁ P₂ f
  where
  module P₁ = Partiality-algebra P₁
  module P₂ = Partiality-algebra P₂

-- The two definitions are isomorphic.

Morphism↔Morphism-as-Σ :
  ∀ {a p₁ p₂ q₁ q₂} {A : Set a}
    {P₁ : Partiality-algebra p₁ q₁ A}
    {P₂ : Partiality-algebra p₂ q₂ A} →
  Morphism P₁ P₂ ↔ Morphism-as-Σ P₁ P₂
Morphism↔Morphism-as-Σ = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ m → function m
                   , monotone m
                   , strict m
                   , now-to-now m
                   , ω-continuous m
      ; from = λ { (f , m , s , n , ω) → record
                   { function     = f
                   ; monotone     = m
                   ; strict       = s
                   ; now-to-now   = n
                   ; ω-continuous = ω
                   }
                 }
      }
    ; right-inverse-of = λ _ → refl
    }
  ; left-inverse-of = λ _ → refl
  }
  where
  open Morphism

abstract

  -- Is-morphism-with is pointwise propositional.

  Is-morphism-with-propositional :
    let open Partiality-algebra in
    ∀ {a p₁ p₂ q₁ q₂} {Type₁ : Set p₁} {Type₂ : Set p₂} {A : Set a}
      (P₁ : Partiality-algebra-with Type₁ q₁ A)
      (P₂ : Partiality-algebra-with Type₂ q₂ A)
      {f : Type₁ → Type₂} →
    Is-proposition (Is-morphism-with P₁ P₂ f)
  Is-morphism-with-propositional _ P₂ =
    Σ-closure 1 (implicit-Π-closure ext 1 λ _ →
                 implicit-Π-closure ext 1 λ _ →
                 Π-closure ext 1 λ _ →
                 P₂.⊑-propositional) λ _ →
    ×-closure 1 (P₂.Type-is-set _ _) $
    ×-closure 1 (Π-closure ext 1 λ _ →
                 P₂.Type-is-set _ _) $
    Π-closure ext 1 λ _ →
    P₂.Type-is-set _ _
    where
    module P₂ = Partiality-algebra-with P₂

  -- Is-morphism is pointwise propositional.

  Is-morphism-propositional :
    let open Partiality-algebra in
    ∀ {a p₁ p₂ q₁ q₂} {A : Set a}
      (P₁ : Partiality-algebra p₁ q₁ A)
      (P₂ : Partiality-algebra p₂ q₂ A)
      {f : Type P₁ → Type P₂} →
    Is-proposition (Is-morphism P₁ P₂ f)
  Is-morphism-propositional P₁ P₂ =
    Is-morphism-with-propositional
      P₁.partiality-algebra-with
      P₂.partiality-algebra-with
    where
    module P₁ = Partiality-algebra P₁
    module P₂ = Partiality-algebra P₂

  -- An equality characterisation lemma for morphisms.

  equality-characterisation-Morphism :
    ∀ {a p₁ p₂ q₁ q₂} {A : Set a}
      {P₁ : Partiality-algebra p₁ q₁ A}
      {P₂ : Partiality-algebra p₂ q₂ A} →
      {m₁ m₂ : Morphism P₁ P₂} →

    Morphism.function m₁ ≡ Morphism.function m₂
      ↔
    m₁ ≡ m₂
  equality-characterisation-Morphism {P₁ = P₁} {P₂} {m₁} {m₂} =
    function m₁ ≡ function m₂                                            ↝⟨ ignore-propositional-component (Is-morphism-propositional P₁ P₂) ⟩
    _↔_.to Morphism↔Morphism-as-Σ m₁ ≡ _↔_.to Morphism↔Morphism-as-Σ m₂  ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ Morphism↔Morphism-as-Σ) ⟩□
    m₁ ≡ m₂                                                              □
    where
    open Morphism

  -- The type of morphisms is a set.

  Morphism-set :
    ∀  {a p₁ p₂ q₁ q₂} {A : Set a}
       {P₁ : Partiality-algebra p₁ q₁ A}
       {P₂ : Partiality-algebra p₂ q₂ A} →
    Is-set (Morphism P₁ P₂)
  Morphism-set {P₂ = P₂} _ _ =
    H-level.respects-surjection
      (_↔_.surjection equality-characterisation-Morphism)
      1
      ((Π-closure ext 2 λ _ → Type-is-set P₂) _ _)
    where
    open Partiality-algebra
