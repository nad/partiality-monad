------------------------------------------------------------------------
-- Pi with partiality algebra families as codomains
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Partiality-algebra.Pi where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Equality.Path.Isomorphisms equality-with-J
  using (ext; ⟨ext⟩)
open import H-level equality-with-J hiding (Type)
open import H-level.Closure equality-with-J

open import Partiality-algebra as PA hiding (id; _∘_)

open Partiality-algebra-with
open Partiality-algebra

-- Applies an increasing sequence of functions to a value.

at-with :
  ∀ {a b p q} {A : Set a} {Type : A → Set p} {B : A → Set b}
  (P : (x : A) → Partiality-algebra-with (Type x) q (B x)) →
  let module P x = Partiality-algebra-with (P x) in
  (∃ λ (f : ℕ → (x : A) → Type x) →
     ∀ n x → P._⊑_ x (f n x) (f (suc n) x)) →
  (x : A) → ∃ λ (f : ℕ → Type x) →
                ∀ n → P._⊑_ x (f n) (f (suc n))
at-with _ s x = Σ-map (λ f n → f n x) (λ f n → f n x) s

-- Applies an increasing sequence of functions to a value.

at :
  ∀ {a b p q} {A : Set a} {B : A → Set b}
  (P : (x : A) → Partiality-algebra p q (B x)) →
  let module P x = Partiality-algebra (P x) in
  (∃ λ (f : ℕ → (x : A) → P.Type x) →
     ∀ n x → P._⊑_ x (f n x) (f (suc n) x)) →
  (x : A) → ∃ λ (f : ℕ → P.Type x) →
                ∀ n → P._⊑_ x (f n) (f (suc n))
at P = at-with (partiality-algebra-with ∘ P)

-- A kind of dependent function space from types to
-- Partiality-algebra-with families.

Π-with : ∀ {a b p q}
         (A : Set a) {Type : A → Set p} {B : A → Set b} →
         ((x : A) → Partiality-algebra-with (Type x) q (B x)) →
         Partiality-algebra-with
           ((x : A) → Type x) (a ⊔ q) ((x : A) → B x)
_⊑_                (Π-with A P) = λ f g → ∀ x → _⊑_ (P x) (f x) (g x)
never              (Π-with A P) = λ x → never (P x)
now                (Π-with A P) = λ f x → now (P x) (f x)
⨆                  (Π-with A P) = λ s x → ⨆ (P x) (at-with P s x)
antisymmetry       (Π-with A P) = λ p q → ⟨ext⟩ λ x →
                                    antisymmetry (P x) (p x) (q x)
Type-is-set-unused (Π-with A P) = Π-closure ext 2 λ x →
                                    Type-is-set-unused (P x)
⊑-refl             (Π-with A P) = λ f x → ⊑-refl (P x) (f x)
⊑-trans            (Π-with A P) = λ f g x → ⊑-trans (P x) (f x) (g x)
never⊑             (Π-with A P) = λ f x → never⊑ (P x) (f x)
upper-bound        (Π-with A P) = λ s n x →
                                    upper-bound (P x) (at-with P s x) n
least-upper-bound  (Π-with A P) = λ s ub is-ub x →
                                    least-upper-bound
                                      (P x) (at-with P s x) (ub x)
                                      (λ n → is-ub n x)
⊑-propositional    (Π-with A P) = Π-closure ext 1 λ x →
                                    ⊑-propositional (P x)

-- A kind of dependent function space from types to partiality algebra
-- families.

Π : ∀ {a b p q} →
    (A : Set a) {B : A → Set b} →
    ((x : A) → Partiality-algebra p q (B x)) →
    Partiality-algebra (a ⊔ p) (a ⊔ q) ((x : A) → B x)
Type                    (Π A P) = (x : A) → Type (P x)
partiality-algebra-with (Π A P) = Π-with A (partiality-algebra-with ∘ P)
