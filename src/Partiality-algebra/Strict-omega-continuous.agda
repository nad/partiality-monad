------------------------------------------------------------------------
-- Strict ω-continuous functions
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Partiality-algebra.Strict-omega-continuous where

open import Equality.Propositional
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms equality-with-J using (ext)
import Equivalence equality-with-J as Eq
open import Function-universe equality-with-J hiding (_∘_)
open import H-level.Closure equality-with-J
open import Monad equality-with-J

open import Partiality-algebra as PA
open import Partiality-algebra.Monotone
open import Partiality-algebra.Omega-continuous

-- Definition of strict ω-continuous functions.

record [_⟶_]⊥
         {a₁ p₁ q₁} {A₁ : Set a₁} (P₁ : Partiality-algebra p₁ q₁ A₁)
         {a₂ p₂ q₂} {A₂ : Set a₂} (P₂ : Partiality-algebra p₂ q₂ A₂) :
         Set (p₁ ⊔ p₂ ⊔ q₁ ⊔ q₂) where
  private
    module P₁ = Partiality-algebra P₁
    module P₂ = Partiality-algebra P₂

  field
    ω-continuous-function : [ P₁ ⟶ P₂ ]

  open [_⟶_] ω-continuous-function public

  field
    strict : function P₁.never ≡ P₂.never

open [_⟶_]⊥

-- Identity.

id⊥ : ∀ {a p q} {A : Set a} {P : Partiality-algebra p q A} →
      [ P ⟶ P ]⊥
ω-continuous-function id⊥ = idω
strict                id⊥ = refl

-- Composition.

infixr 40 _∘⊥_

_∘⊥_ :
  ∀ {a₁ p₁ q₁} {A₁ : Set a₁} {P₁ : Partiality-algebra p₁ q₁ A₁}
    {a₂ p₂ q₂} {A₂ : Set a₂} {P₂ : Partiality-algebra p₂ q₂ A₂}
    {a₃ p₃ q₃} {A₃ : Set a₃} {P₃ : Partiality-algebra p₃ q₃ A₃} →
  [ P₂ ⟶ P₃ ]⊥ → [ P₁ ⟶ P₂ ]⊥ → [ P₁ ⟶ P₃ ]⊥
ω-continuous-function (f ∘⊥ g) =
  ω-continuous-function f ∘ω ω-continuous-function g

strict (_∘⊥_ {P₁ = P₁} {P₂ = P₂} {P₃ = P₃} f g) =
  function f (function g P₁.never)  ≡⟨ cong (function f) (strict g) ⟩
  function f P₂.never               ≡⟨ strict f ⟩∎
  P₃.never                          ∎
  where
  module P₁ = Partiality-algebra P₁
  module P₂ = Partiality-algebra P₂
  module P₃ = Partiality-algebra P₃

-- Equality characterisation lemma for strict ω-continuous functions.

equality-characterisation-strict :
  ∀ {a₁ p₁ q₁} {A₁ : Set a₁} {P₁ : Partiality-algebra p₁ q₁ A₁}
    {a₂ p₂ q₂} {A₂ : Set a₂} {P₂ : Partiality-algebra p₂ q₂ A₂}
    {f g : [ P₁ ⟶ P₂ ]⊥} →
  (∀ x → function f x ≡ function g x) ↔ f ≡ g
equality-characterisation-strict {P₁ = P₁} {P₂ = P₂} {f} {g} =
  (∀ x → function f x ≡ function g x)                ↝⟨ equality-characterisation-continuous ⟩
  ω-continuous-function f ≡ ω-continuous-function g  ↝⟨ ignore-propositional-component P₂.Type-is-set ⟩
  _↔_.to rearrange f ≡ _↔_.to rearrange g            ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ rearrange) ⟩□
  f ≡ g                                              □
  where
  module P₁ = Partiality-algebra P₁
  module P₂ = Partiality-algebra P₂

  rearrange :
    [ P₁ ⟶ P₂ ]⊥
      ↔
    ∃ λ (h : [ P₁ ⟶ P₂ ]) → [_⟶_].function h P₁.never ≡ P₂.never
  rearrange = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ f → ω-continuous-function f , strict f
        ; from = uncurry λ f c → record { ω-continuous-function = f
                                        ; strict                = c
                                        }
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ _ → refl
    }
    where
    open Partiality-algebra

-- Composition is associative.

∘⊥-assoc :
  ∀ {a₁ p₁ q₁} {A₁ : Set a₁} {P₁ : Partiality-algebra p₁ q₁ A₁}
    {a₂ p₂ q₂} {A₂ : Set a₂} {P₂ : Partiality-algebra p₂ q₂ A₂}
    {a₃ p₃ q₃} {A₃ : Set a₃} {P₃ : Partiality-algebra p₃ q₃ A₃}
    {a₄ p₄ q₄} {A₄ : Set a₄} {P₄ : Partiality-algebra p₄ q₄ A₄}
  (f : [ P₃ ⟶ P₄ ]⊥) (g : [ P₂ ⟶ P₃ ]⊥) (h : [ P₁ ⟶ P₂ ]⊥) →
  f ∘⊥ (g ∘⊥ h) ≡ (f ∘⊥ g) ∘⊥ h
∘⊥-assoc _ _ _ =
  _↔_.to equality-characterisation-strict λ _ → refl
