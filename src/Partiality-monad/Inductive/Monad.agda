------------------------------------------------------------------------
-- The partiality monad's monad instance
------------------------------------------------------------------------

{-# OPTIONS --without-K --rewriting #-}

module Partiality-monad.Inductive.Monad where

open import Equality.Propositional
import Monad
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Eliminators
open import Partiality-monad.Inductive.Omega-continuous
open import Partiality-monad.Inductive.Properties

------------------------------------------------------------------------
-- The monad instance

-- Functions of type A → B ⊥ can be lifted to /ω-continuous/ functions
-- from A ⊥ to B ⊥.

module _ {a b} {A : Set a} {B : Set b} (f : A → B ⊥) where

  private

    =<<-args : Rec-args-nd A (B ⊥) _⊑_
    =<<-args = record
      { pe = never
      ; po = f
      ; pl = λ _ → ⨆
      ; pa = λ _ _ → antisymmetry
      ; qr = λ _ → ⊑-refl
      ; qe = λ _ → never⊑
      ; qu = λ _ _ _ n pq pu ⨆pq⊑pu →
               upper-bound′ pq pu ⨆pq⊑pu n
      ; ql = λ _ _ _ → least-upper-bound
      ; qp = λ _ _ → ⊑-propositional
      }

  infix 50 _∗ _∗-inc_

  _∗ : [ A ⊥→ B ⊥]
  _∗ = (⊥-rec-nd =<<-args , ⊑-rec-nd =<<-args) , λ _ → refl

  _∗-inc_ : Increasing-sequence A → Increasing-sequence B
  _∗-inc_ = inc-rec-nd =<<-args

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ : ∀ {a b} {A : Set a} {B : Set b} →
         A ⊥ → (A → B ⊥) → B ⊥
x >>=′ f = proj₁ (proj₁ (f ∗)) x

-- Bind is monotone.

infixl 5 _>>=-mono_

_>>=-mono_ :
  ∀ {a b} {A : Set a} {B : Set b} {x y : A ⊥} {f g : A → B ⊥} →
  x ⊑ y → (∀ z → f z ⊑ g z) → x >>=′ f ⊑ y >>=′ g
_>>=-mono_ {x = x} {y} {f} {g} x⊑y f⊑g =
  x >>=′ f ⊑⟨ proj₂ (proj₁ (f ∗)) x⊑y ⟩
  y >>=′ f ⊑⟨ ⊥-rec-Prop {P = λ y → y >>=′ f ⊑ y >>=′ g} (record
                { pe = never⊑ never
                ; po = f⊑g
                ; pl = λ s ih →
                         ⨆ s >>=′ f     ⊑⟨⟩
                         ⨆ (f ∗-inc s)  ⊑⟨ ⨆-mono ih ⟩
                         ⨆ (g ∗-inc s)  ⊑⟨⟩
                         ⨆ s >>=′ g     ■
                ; pp = λ _ → ⊑-propositional
                })
                y ⟩
  y >>=′ g ■

-- Instances of the monad laws with extra universe polymorphism.

module Monad-laws where

  left-identity : ∀ {a b} {A : Set a} {B : Set b} x (f : A → B ⊥) →
                  now x >>=′ f ≡ f x
  left-identity x f = refl

  right-identity : ∀ {a} {A : Set a} (x : A ⊥) →
                   x >>=′ now ≡ x
  right-identity = ⊥-rec-Prop
    (record
       { pe = refl
       ; po = λ _ → refl
       ; pl = λ s hyp →
                ⨆ s >>=′ now        ≡⟨⟩
                ⨆ (now ∗-inc s)     ≡⟨ cong ⨆ (_↔_.to equality-characterisation-increasing λ n →

                  s [ n ] >>=′ now       ≡⟨ hyp n ⟩∎
                  s [ n ]                ∎) ⟩∎

                ⨆ s                 ∎
       ; pp = λ _ → ⊥-is-set _ _
       })

  associativity : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
                  (x : A ⊥) (f : A → B ⊥) (g : B → C ⊥) →
                  x >>=′ (λ x → f x >>=′ g) ≡ x >>=′ f >>=′ g
  associativity x f g = ⊥-rec-Prop
    (record
       { pe = refl
       ; po = λ _ → refl
       ; pl = λ s hyp →
                ⨆ ((λ x → f x >>=′ g) ∗-inc s)     ≡⟨ cong ⨆ (_↔_.to equality-characterisation-increasing λ n →

                  s [ n ] >>=′ (λ x → f x >>=′ g)       ≡⟨ hyp n ⟩∎
                  s [ n ] >>=′ f >>=′ g                 ∎) ⟩∎

                ⨆ (g ∗-inc (f ∗-inc s))            ∎
       ; pp = λ _ → ⊥-is-set _ _
       })
    x

open Monad equality-with-J hiding (map; map-id; map-∘)

instance

  -- The partiality monad's monad instance.

  partiality-monad : ∀ {ℓ} → Monad (_⊥ {a = ℓ})
  Raw-monad.return (Monad.raw-monad partiality-monad) = now
  Raw-monad._>>=_  (Monad.raw-monad partiality-monad) = _>>=′_
  Monad.left-identity  partiality-monad = Monad-laws.left-identity
  Monad.right-identity partiality-monad = Monad-laws.right-identity
  Monad.associativity  partiality-monad = Monad-laws.associativity

------------------------------------------------------------------------
-- _⊥ is a functor

map : ∀ {a b} {A : Set a} {B : Set b} →
      (A → B) → [ A ⊥→ B ⊥]
map f = (return ∘ f) ∗

map-id : ∀ {a} {A : Set a} →
         map (id {A = A}) ≡ idω
map-id =
  return ∗  ≡⟨ _↔_.to equality-characterisation-continuous (λ x →

    x >>= return  ≡⟨ right-identity x ⟩∎
    x             ∎) ⟩∎

  idω       ∎

map-∘ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
        (f : B → C) (g : A → B) →
        map (f ∘ g) ≡ map f ∘ω map g
map-∘ f g =
  (now ∘ f ∘ g) ∗                ≡⟨ _↔_.to equality-characterisation-continuous (λ x →

    x >>=′ (now ∘ f ∘ g)                     ≡⟨⟩
    x >>=′ (λ x → now (g x) >>=′ (now ∘ f))  ≡⟨ Monad-laws.associativity x (now ∘ g) (now ∘ f) ⟩∎
    x >>=′ (now ∘ g) >>=′ (now ∘ f)          ∎) ⟩∎

  (now ∘ f) ∗ ∘ω (now ∘ g) ∗  ∎
