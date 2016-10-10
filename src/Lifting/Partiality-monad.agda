------------------------------------------------------------------------
-- An alternative but equivalent definition of the partiality monad,
-- based on the lifting construction in Lifting
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

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
    ; pp = _⇔_.to set⇔UIP IP.⊥-is-set
    ; qr = λ _ → I.⊑-refl
    ; qt = λ _ _ _ _ _ → I.⊑-trans
    ; qe = λ _ → I.never⊑
    ; qu = λ _ → I.upper-bound
    ; ql = λ _ _ _ → I.least-upper-bound
    ; qm = λ { refl → I.⊑-refl _ }
    ; q⨆ = λ s →
             I.now (proj₁ s 0)                    IP.⊑⟨ I.upper-bound _ 0 ⟩■
             I.⨆ ((λ n → I.now (proj₁ s n)) , _)  ■
    ; qp = λ _ _ _ → I.⊑-proof-irrelevant
    }

  argsI : ∀ {A} → IE.Rec-args-nd A (A ⊥) _⊑_
  argsI = record
    { pe = L.never
    ; po = L.now
    ; pl = λ _ → L.⨆
    ; pa = λ _ _ → L.antisymmetry
    ; ps = L.Carrier-is-set
    ; qr = λ _ → L.⊑-refl
    ; qt = λ _ _ → L.⊑-trans
    ; qe = λ _ → L.never⊑
    ; qu = λ _ → L.upper-bound
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
        { pe = L.⊥-rec argsL (IE.⊥-rec-nd argsI I.never)  ≡⟨ cong (L.⊥-rec argsL) (IE.⊥-rec-nd-never argsI) ⟩
               L.⊥-rec argsL L.never                      ≡⟨ L.⊥-rec-never _ ⟩∎
               I.never                                    ∎
        ; po = λ x →
                 L.⊥-rec argsL (IE.⊥-rec-nd argsI (I.now x))  ≡⟨ cong (L.⊥-rec argsL) (IE.⊥-rec-nd-now argsI _) ⟩
                 L.⊥-rec argsL (L.now x)                      ≡⟨ L.⊥-rec-now _ _ ⟩∎
                 I.now x ∎
        ; pl = λ s ih →
                 L.⊥-rec argsL (IE.⊥-rec-nd argsI (I.⨆ s))      ≡⟨ cong (L.⊥-rec argsL) (IE.⊥-rec-nd-⨆ argsI _) ⟩
                 L.⊥-rec argsL (L.⨆ (IE.inc-rec-nd argsI s))    ≡⟨ L.⊥-rec-⨆ _ _ ⟩
                 I.⨆ (L.inc-rec argsL (IE.inc-rec-nd argsI s))  ≡⟨ cong I.⨆ $ _↔_.to IP.equality-characterisation-increasing ih ⟩∎
                 I.⨆ s                                          ∎
        ; pp = λ _ → IP.⊥-is-set _ _
        })
    }
  ; left-inverse-of = L.⊥-rec {Q = λ _ _ _ → ⊤} (record
      { pe = IE.⊥-rec-nd argsI (L.⊥-rec argsL L.never)  ≡⟨ cong (IE.⊥-rec-nd argsI) (L.⊥-rec-never _) ⟩
             IE.⊥-rec-nd argsI I.never                  ≡⟨ IE.⊥-rec-nd-never argsI ⟩∎
             L.never                                    ∎
      ; po = λ x →
               IE.⊥-rec-nd argsI (L.⊥-rec argsL (L.now x))  ≡⟨ cong (IE.⊥-rec-nd argsI) (L.⊥-rec-now _ _) ⟩
               IE.⊥-rec-nd argsI (I.now x)                  ≡⟨ IE.⊥-rec-nd-now argsI _ ⟩∎
               L.now x                                      ∎
      ; pl = λ s ih →
                 IE.⊥-rec-nd argsI (L.⊥-rec argsL (L.⨆ s))      ≡⟨ cong (IE.⊥-rec-nd argsI) (L.⊥-rec-⨆ _ _) ⟩
                 IE.⊥-rec-nd argsI (I.⨆ (L.inc-rec argsL s))    ≡⟨ IE.⊥-rec-nd-⨆ argsI _ ⟩
                 L.⨆ (IE.inc-rec-nd argsI (L.inc-rec argsL s))  ≡⟨ cong L.⨆ $ _↔_.to L.equality-characterisation-increasing (proj₁ ih) ⟩∎
                 L.⨆ s                                          ∎
      ; pa = λ _ _ _ _ _ _ →
               _⇔_.to set⇔UIP L.Carrier-is-set _ _
      ; pp = _⇔_.to set⇔UIP (mono₁ 1 (L.Carrier-is-set _ _))
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
