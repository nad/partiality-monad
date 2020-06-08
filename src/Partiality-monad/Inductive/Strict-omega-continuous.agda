------------------------------------------------------------------------
-- Strict ω-continuous functions
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Partiality-monad.Inductive.Strict-omega-continuous where

open import Equality.Propositional.Cubical
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J hiding (_∘_)
open import Monad equality-with-J

import Partiality-algebra.Strict-omega-continuous as S
open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Eliminators
open import Partiality-monad.Inductive.Monad
open import Partiality-monad.Inductive.Monotone
open import Partiality-monad.Inductive.Omega-continuous

-- Definition of strict ω-continuous functions.

[_⊥→_⊥]-strict : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
[ A ⊥→ B ⊥]-strict = S.[ partiality-algebra A ⟶ partiality-algebra B ]⊥

module [_⊥→_⊥]-strict
         {a b} {A : Set a} {B : Set b}
         (f : [ A ⊥→ B ⊥]-strict) =
         S.[_⟶_]⊥ f

open [_⊥→_⊥]-strict

-- Identity.

id-strict : ∀ {a} {A : Set a} → [ A ⊥→ A ⊥]-strict
id-strict = S.id⊥

-- Composition.

infixr 40 _∘-strict_

_∘-strict_ :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
  [ B ⊥→ C ⊥]-strict → [ A ⊥→ B ⊥]-strict → [ A ⊥→ C ⊥]-strict
_∘-strict_ = S._∘⊥_

-- Equality characterisation lemma for strict ω-continuous functions.

equality-characterisation-strict :
  ∀ {a b} {A : Set a} {B : Set b} {f g : [ A ⊥→ B ⊥]-strict} →
  (∀ x → function f x ≡ function g x) ↔ f ≡ g
equality-characterisation-strict =
  S.equality-characterisation-strict

-- Composition is associative.

∘-strict-assoc :
  ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  (f : [ C ⊥→ D ⊥]-strict) (g : [ B ⊥→ C ⊥]-strict)
  (h : [ A ⊥→ B ⊥]-strict) →
  f ∘-strict (g ∘-strict h) ≡ (f ∘-strict g) ∘-strict h
∘-strict-assoc = S.∘⊥-assoc

-- Strict ω-continuous functions satisfy an extra monad law.

>>=-∘-return :
  ∀ {a b} {A : Set a} {B : Set b} →
  (f : [ A ⊥→ B ⊥]-strict) →
  ∀ x → x >>=′ (function f ∘ return) ≡ function f x
>>=-∘-return fs = ⊥-rec-⊥
  (record
     { P  = λ x → x >>=′ (f ∘ return) ≡ f x
     ; pe = never >>=′ f ∘ return  ≡⟨ never->>= ⟩
            never                  ≡⟨ sym (strict fs) ⟩∎
            f never                ∎
     ; po = λ x →
              now x >>=′ f ∘ return  ≡⟨ now->>= ⟩∎
              f (now x)              ∎
     ; pl = λ s p →
              ⨆ s >>=′ (f ∘ return)     ≡⟨ ⨆->>= ⟩
              ⨆ ((f ∘ return) ∗-inc s)  ≡⟨ cong ⨆ (_↔_.to equality-characterisation-increasing λ n →

                (f ∘ return) ∗-inc s [ n ]   ≡⟨ p n ⟩∎
                [ f⊑ $ s ]-inc [ n ]         ∎) ⟩

              ⨆ [ f⊑ $ s ]-inc          ≡⟨ sym $ ω-continuous fs s ⟩∎
              f (⨆ s)                   ∎
     ; pp = λ _ → ⊥-is-set
     })
  where
  f⊑ = monotone-function fs
  f  = function fs

-- Strict ω-continuous functions from A ⊥ to B ⊥ are isomorphic to
-- functions from A to B ⊥.

partial↔strict :
  ∀ {a b} {A : Set a} {B : Set b} →
  (A → B ⊥) ↔ [ A ⊥→ B ⊥]-strict
partial↔strict {a} = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ f → record
                 { ω-continuous-function = f ∗
                 ; strict                =
                     never >>=′ f  ≡⟨ never->>= ⟩∎
                     never         ∎
                 }
      ; from = λ f x → function f (return x)
      }
    ; right-inverse-of = λ f →
        _↔_.to equality-characterisation-strict λ x →
          x >>=′ (function f ∘ return)  ≡⟨ >>=-∘-return f x ⟩∎
          function f x                  ∎
    }
  ; left-inverse-of = λ f → ⟨ext⟩ λ x →
      return x >>=′ f  ≡⟨ Monad-laws.left-identity x f ⟩∎
      f x              ∎
  }
