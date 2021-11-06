------------------------------------------------------------------------
-- Monotone functions
------------------------------------------------------------------------

{-# OPTIONS --erased-cubical --safe #-}

module Partiality-algebra.Monotone where

open import Equality.Propositional.Cubical
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
import Equivalence equality-with-J as Eq
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level.Closure equality-with-J

open import Partiality-algebra as PA hiding (id; _∘_)
import Partiality-algebra.Properties as PAP

-- Definition of monotone functions.

record [_⟶_]⊑
         {a₁ p₁ q₁} {A₁ : Type a₁} (P₁ : Partiality-algebra p₁ q₁ A₁)
         {a₂ p₂ q₂} {A₂ : Type a₂} (P₂ : Partiality-algebra p₂ q₂ A₂) :
         Type (p₁ ⊔ p₂ ⊔ q₁ ⊔ q₂) where
  private
    module P₁ = Partiality-algebra P₁
    module P₂ = Partiality-algebra P₂

  field
    function : P₁.T → P₂.T
    monotone : ∀ {x y} → x P₁.⊑ y → function x P₂.⊑ function y

open [_⟶_]⊑

-- Identity.

id⊑ : ∀ {a p q} {A : Type a} {P : Partiality-algebra p q A} →
      [ P ⟶ P ]⊑
function id⊑ = id
monotone id⊑ = id

-- Composition.

infixr 40 _∘⊑_

_∘⊑_ :
  ∀ {a₁ p₁ q₁} {A₁ : Type a₁} {P₁ : Partiality-algebra p₁ q₁ A₁}
    {a₂ p₂ q₂} {A₂ : Type a₂} {P₂ : Partiality-algebra p₂ q₂ A₂}
    {a₃ p₃ q₃} {A₃ : Type a₃} {P₃ : Partiality-algebra p₃ q₃ A₃} →
  [ P₂ ⟶ P₃ ]⊑ → [ P₁ ⟶ P₂ ]⊑ → [ P₁ ⟶ P₃ ]⊑
function (f ∘⊑ g) = function f ∘ function g
monotone (f ∘⊑ g) = monotone f ∘ monotone g

-- Equality characterisation lemma for monotone functions.

equality-characterisation-monotone :
  ∀ {a₁ p₁ q₁} {A₁ : Type a₁} {P₁ : Partiality-algebra p₁ q₁ A₁}
    {a₂ p₂ q₂} {A₂ : Type a₂} {P₂ : Partiality-algebra p₂ q₂ A₂}
    {f g : [ P₁ ⟶ P₂ ]⊑} →
  (∀ x → function f x ≡ function g x) ↔ f ≡ g
equality-characterisation-monotone {P₁ = P₁} {P₂ = P₂} {f} {g} =
  (∀ x → function f x ≡ function g x)                                   ↔⟨ Eq.extensionality-isomorphism ext ⟩

  function f ≡ function g                                               ↝⟨ ignore-propositional-component
                                                                             (implicit-Π-closure ext 1 λ _ →
                                                                              implicit-Π-closure ext 1 λ _ →
                                                                              Π-closure          ext 1 λ _ →
                                                                              P₂.⊑-propositional) ⟩
  _↔_.to rearrange f ≡ _↔_.to rearrange g                               ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ rearrange) ⟩□

  f ≡ g                                                                 □
  where
  module P₁ = Partiality-algebra P₁
  module P₂ = Partiality-algebra P₂

  rearrange :
    [ P₁ ⟶ P₂ ]⊑
      ↔
    ∃ λ (h : P₁.T → P₂.T) →
      ∀ {x y} → x P₁.⊑ y → h x P₂.⊑ h y
  rearrange = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ f → function f , monotone f
        ; from = uncurry λ f m → record { function = f; monotone = m }
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ _ → refl
    }
    where
    open Partiality-algebra

-- Composition is associative.

∘⊑-assoc :
  ∀ {a₁ p₁ q₁} {A₁ : Type a₁} {P₁ : Partiality-algebra p₁ q₁ A₁}
    {a₂ p₂ q₂} {A₂ : Type a₂} {P₂ : Partiality-algebra p₂ q₂ A₂}
    {a₃ p₃ q₃} {A₃ : Type a₃} {P₃ : Partiality-algebra p₃ q₃ A₃}
    {a₄ p₄ q₄} {A₄ : Type a₄} {P₄ : Partiality-algebra p₄ q₄ A₄}
  (f : [ P₃ ⟶ P₄ ]⊑) (g : [ P₂ ⟶ P₃ ]⊑) {h : [ P₁ ⟶ P₂ ]⊑} →
  f ∘⊑ (g ∘⊑ h) ≡ (f ∘⊑ g) ∘⊑ h
∘⊑-assoc _ _ =
  _↔_.to equality-characterisation-monotone λ _ → refl

module _
  {a₁ p₁ q₁} {A₁ : Type a₁} {P₁ : Partiality-algebra p₁ q₁ A₁}
  {a₂ p₂ q₂} {A₂ : Type a₂} {P₂ : Partiality-algebra p₂ q₂ A₂} where

  private
    module P₁   = Partiality-algebra P₁
    module P₂   = Partiality-algebra P₂
    module PAP₁ = PAP P₁
    module PAP₂ = PAP P₂

  -- If a monotone function is applied to an increasing sequence,
  -- then the result is another increasing sequence.

  [_$_]-inc :
    [ P₁ ⟶ P₂ ]⊑ → P₁.Increasing-sequence → P₂.Increasing-sequence
  [ f $ s ]-inc = (λ n → function f (s P₁.[ n ]))
                , (λ n → monotone f (P₁.increasing s n))

  -- A lemma relating monotone functions and least upper bounds.

  ⨆$⊑$⨆ : (f : [ P₁ ⟶ P₂ ]⊑) →
          ∀ s → P₂.⨆ [ f $ s ]-inc P₂.⊑ function f (P₁.⨆ s)
  ⨆$⊑$⨆ f s = P₂.least-upper-bound _ _ λ n →

    [ f $ s ]-inc P₂.[ n ]  PAP₂.⊑⟨ monotone f (

        s P₁.[ n ]                    PAP₁.⊑⟨ P₁.upper-bound _ _ ⟩■
        P₁.⨆ s                        ■) ⟩■

    function f (P₁.⨆ s)     ■
