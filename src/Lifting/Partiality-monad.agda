------------------------------------------------------------------------
-- An alternative but equivalent definition of the partiality monad,
-- based on the lifting construction in Lifting
------------------------------------------------------------------------

{-# OPTIONS --without-K --rewriting #-}

open import Prelude hiding (⊥)

module Lifting.Partiality-monad {a : Level} where

open import Equality.Propositional
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)

open import Bijection equality-with-J using (_↔_)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J hiding (⊥↔⊥)
open import H-level equality-with-J

import Lifting
open import Omega-CPO
import Partiality-monad.Inductive as I
import Partiality-monad.Inductive.Eliminators as IE
import Partiality-monad.Inductive.Properties as IP

private
  module L {A : Set a} = Lifting (Type→ω-CPO A)

-- The partiality monad as an ω-CPPO.

partiality-monad : Set a → ω-CPPO a
partiality-monad A = L.cppo {A = A}

-- The partiality monad.

infix 10 _⊥
infix  4 _⊑_

_⊥ : Set a → Set a
A ⊥ = ω-CPPO.Carrier (partiality-monad A)

_⊑_ : ∀ {A} → A ⊥ → A ⊥ → Set a
_⊑_ {A = A} = ω-CPPO._⊑_ (partiality-monad A)

-- This definition of the partiality monad is isomorphic to the
-- definition in Partiality-monad.Inductive.

private

  argsL : ∀ {A} → L.Rec-args (λ (_ : A ⊥) → A I.⊥) (λ x y _ → x I.⊑ y)
  argsL = record
    { pe = I.never
    ; po = I.now
    ; pl = λ _ → I.⨆
    ; pa = λ x⊑y y⊑x p-x p-y p-x⊑p-y p-y⊑p-x →
             subst (const _) (L.antisymmetry x⊑y y⊑x) p-x  ≡⟨ subst-const (L.antisymmetry x⊑y y⊑x) ⟩
             p-x                                           ≡⟨ I.antisymmetry p-x⊑p-y p-y⊑p-x ⟩∎
             p-y                                           ∎
    ; qr = λ _ → I.⊑-refl
    ; qt = λ _ _ _ _ _ → IP.⊑-trans
    ; qe = λ _ → I.never⊑
    ; qu = λ _ → IP.upper-bound
    ; ql = λ _ _ _ → I.least-upper-bound
    ; qm = λ { refl → I.⊑-refl _ }
    ; q⨆ = λ s →
             I.now (proj₁ s 0)                    IP.⊑⟨ IP.upper-bound _ 0 ⟩■
             I.⨆ ((λ n → I.now (proj₁ s n)) , _)  ■
    ; qp = λ _ _ _ → I.⊑-proof-irrelevant
    }

  argsI : ∀ {A} → IE.Rec-args-nd A (A ⊥) _⊑_
  argsI = record
    { pe = L.never
    ; po = L.now
    ; pl = λ _ → L.⨆
    ; pa = λ _ _ → L.antisymmetry
    ; qr = λ _ → L.⊑-refl
    ; qe = λ _ → L.never⊑
    ; qu = λ _ _ _ _ _ qu _ →
             L.⊑-trans _ _ _ (L.upper-bound _ _) qu
    ; ql = λ _ _ _ → L.least-upper-bound
    ; qp = λ _ _ → L.⊑-propositional
    }

⊥↔⊥ : ∀ {A} → A ⊥ ↔ A I.⊥
⊥↔⊥ = record
  { surjection = record
    { logical-equivalence = record
      { to   = L.⊥-rec argsL
      ; from = IE.⊥-rec-nd argsI
      }
    ; right-inverse-of = IE.⊥-rec-⊥ (record
        { pe = refl
        ; po = λ _ → refl
        ; pl = λ s ih →
                 I.⨆ (L.inc-rec argsL (IE.inc-rec-nd argsI s))  ≡⟨ cong I.⨆ $ _↔_.to IP.equality-characterisation-increasing ih ⟩∎
                 I.⨆ s                                          ∎
        ; pp = λ _ → IP.⊥-is-set _ _
        })
    }
  ; left-inverse-of = L.⊥-rec {Q = λ _ _ _ → ⊤} (record
      { pe = refl
      ; po = λ _ → refl
      ; pl = λ s ih →
                 L.⨆ (IE.inc-rec-nd argsI (L.inc-rec argsL s))  ≡⟨ cong L.⨆ $ _↔_.to L.equality-characterisation-increasing (proj₁ ih) ⟩∎
                 L.⨆ s                                          ∎
      ; pa = λ _ _ _ _ _ _ →
               _⇔_.to set⇔UIP L.Carrier-is-set _ _
      ; qp = λ _ _ _ _ _ → refl
      })
  }

⊑≃⊑ : ∀ {A} {x y : A ⊥} →
      (x ⊑ y) ≃ (_↔_.to ⊥↔⊥ x I.⊑ _↔_.to ⊥↔⊥ y)
⊑≃⊑ {x = x} {y} =
  _↔_.to (Eq.⇔↔≃ ext L.⊑-propositional IP.⊑-propositional)
    (record
       { to   = L.⊑-rec argsL
       ; from =
                _↔_.to ⊥↔⊥ x I.⊑ _↔_.to ⊥↔⊥ y  ↝⟨ IE.⊑-rec-nd argsI ⟩

                _↔_.from ⊥↔⊥ (_↔_.to ⊥↔⊥ x) ⊑
                _↔_.from ⊥↔⊥ (_↔_.to ⊥↔⊥ y)    ↝⟨ ≡⇒↝ _ (cong₂ _⊑_ (_↔_.left-inverse-of ⊥↔⊥ _)
                                                                   (_↔_.left-inverse-of ⊥↔⊥ _)) ⟩□
                x ⊑ y                          □
       })
