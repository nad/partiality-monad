------------------------------------------------------------------------
-- ω-continuous functions
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Partiality-algebra.Omega-continuous where

open import Equality.Propositional.Cubical
open import Prelude

open import Bijection equality-with-J using (_↔_)
import Equivalence equality-with-J as Eq
open import Function-universe equality-with-J
open import H-level.Closure equality-with-J

open import Partiality-algebra as PA
open import Partiality-algebra.Monotone

-- Definition of ω-continuous functions.

record [_⟶_]
         {a₁ p₁ q₁} {A₁ : Type a₁} (P₁ : Partiality-algebra p₁ q₁ A₁)
         {a₂ p₂ q₂} {A₂ : Type a₂} (P₂ : Partiality-algebra p₂ q₂ A₂) :
         Type (p₁ ⊔ p₂ ⊔ q₁ ⊔ q₂) where
  private
    module P₁ = Partiality-algebra P₁
    module P₂ = Partiality-algebra P₂

  field
    monotone-function : [ P₁ ⟶ P₂ ]⊑

  open [_⟶_]⊑ monotone-function public

  field
    ω-continuous :
      ∀ s → function (P₁.⨆ s) ≡ P₂.⨆ [ monotone-function $ s ]-inc

open [_⟶_]

-- Identity.

idω : ∀ {a p q} {A : Type a} {P : Partiality-algebra p q A} →
      [ P ⟶ P ]
monotone-function idω   = id⊑
ω-continuous      idω _ = refl

-- Composition.

infixr 40 _∘ω_

_∘ω_ :
  ∀ {a₁ p₁ q₁} {A₁ : Type a₁} {P₁ : Partiality-algebra p₁ q₁ A₁}
    {a₂ p₂ q₂} {A₂ : Type a₂} {P₂ : Partiality-algebra p₂ q₂ A₂}
    {a₃ p₃ q₃} {A₃ : Type a₃} {P₃ : Partiality-algebra p₃ q₃ A₃} →
  [ P₂ ⟶ P₃ ] → [ P₁ ⟶ P₂ ] → [ P₁ ⟶ P₃ ]
monotone-function (f ∘ω g) = monotone-function f ∘⊑ monotone-function g

ω-continuous (_∘ω_ {P₁ = P₁} {P₂ = P₂} {P₃ = P₃} f g) s =
  function f (function g (P₁.⨆ s))                             ≡⟨ cong (function f) (ω-continuous g s) ⟩
  function f (P₂.⨆ [ monotone-function g $ s ]-inc)            ≡⟨ ω-continuous f _ ⟩∎
  P₃.⨆ [ monotone-function f ∘⊑ monotone-function g $ s ]-inc  ∎
  where
  module P₁ = Partiality-algebra P₁
  module P₂ = Partiality-algebra P₂
  module P₃ = Partiality-algebra P₃

-- Equality characterisation lemma for ω-continuous functions.

equality-characterisation-continuous :
  ∀ {a₁ p₁ q₁} {A₁ : Type a₁} {P₁ : Partiality-algebra p₁ q₁ A₁}
    {a₂ p₂ q₂} {A₂ : Type a₂} {P₂ : Partiality-algebra p₂ q₂ A₂}
    {f g : [ P₁ ⟶ P₂ ]} →
  (∀ x → function f x ≡ function g x) ↔ f ≡ g
equality-characterisation-continuous {P₁ = P₁} {P₂ = P₂} {f} {g} =
  (∀ x → function f x ≡ function g x)        ↝⟨ equality-characterisation-monotone ⟩
  monotone-function f ≡ monotone-function g  ↝⟨ ignore-propositional-component
                                                  (Π-closure ext 1 λ _ →
                                                   P₂.T-is-set) ⟩
  _↔_.to rearrange f ≡ _↔_.to rearrange g    ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ rearrange) ⟩□
  f ≡ g                                      □
  where
  module P₁ = Partiality-algebra P₁
  module P₂ = Partiality-algebra P₂

  rearrange :
    [ P₁ ⟶ P₂ ]
      ↔
    ∃ λ (h : [ P₁ ⟶ P₂ ]⊑) →
      ∀ s → [_⟶_]⊑.function h (P₁.⨆ s) ≡ P₂.⨆ [ h $ s ]-inc
  rearrange = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ f → monotone-function f , ω-continuous f
        ; from = uncurry λ f c → record { monotone-function = f
                                        ; ω-continuous      = c
                                        }
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ _ → refl
    }
    where
    open Partiality-algebra

-- Composition is associative.

∘ω-assoc :
  ∀ {a₁ p₁ q₁} {A₁ : Type a₁} {P₁ : Partiality-algebra p₁ q₁ A₁}
    {a₂ p₂ q₂} {A₂ : Type a₂} {P₂ : Partiality-algebra p₂ q₂ A₂}
    {a₃ p₃ q₃} {A₃ : Type a₃} {P₃ : Partiality-algebra p₃ q₃ A₃}
    {a₄ p₄ q₄} {A₄ : Type a₄} {P₄ : Partiality-algebra p₄ q₄ A₄}
  (f : [ P₃ ⟶ P₄ ]) (g : [ P₂ ⟶ P₃ ]) (h : [ P₁ ⟶ P₂ ]) →
  f ∘ω (g ∘ω h) ≡ (f ∘ω g) ∘ω h
∘ω-assoc _ _ _ =
  _↔_.to equality-characterisation-continuous λ _ → refl
