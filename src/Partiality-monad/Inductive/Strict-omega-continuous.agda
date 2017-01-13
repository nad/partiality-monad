------------------------------------------------------------------------
-- Strict ω-continuous functions
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Partiality-monad.Inductive.Strict-omega-continuous where

open import Equality.Propositional
open import Interval using (ext)
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J hiding (_∘_)
open import Monad equality-with-J

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Eliminators
open import Partiality-monad.Inductive.Monad
open import Partiality-monad.Inductive.Monotone
open import Partiality-monad.Inductive.Omega-continuous

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

-- Composition is associative.

∘-strict-assoc :
  ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  (f : [ C ⊥→ D ⊥]-strict) (g : [ B ⊥→ C ⊥]-strict)
  (h : [ A ⊥→ B ⊥]-strict) →
  f ∘-strict (g ∘-strict h) ≡ (f ∘-strict g) ∘-strict h
∘-strict-assoc _ _ _ =
  _↔_.to equality-characterisation-strict λ _ → refl

-- Strict ω-continuous functions satisfy an extra monad law.

>>=-∘-return :
  ∀ {a b} {A : Set a} {B : Set b} →
  (fs : [ A ⊥→ B ⊥]-strict) →
  let f = proj₁ (proj₁ (proj₁ fs)) in
  ∀ x → x >>=′ (f ∘ return) ≡ f x
>>=-∘-return fs = ⊥-rec-⊥
  (record
     { P  = λ x → x >>=′ (f ∘ return) ≡ f x
     ; pe = never >>=′ f ∘ return  ≡⟨ never->>= ⟩
            never                  ≡⟨ sym (proj₂ fs) ⟩∎
            f never                ∎
     ; po = λ x →
              now x >>=′ f ∘ return  ≡⟨ now->>= ⟩∎
              f (now x)              ∎
     ; pl = λ s p →
              ⨆ s >>=′ (f ∘ return)     ≡⟨ ⨆->>= ⟩
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
      { to   = λ f → f ∗ , (never >>=′ f  ≡⟨ never->>= ⟩∎
                            never         ∎)
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
