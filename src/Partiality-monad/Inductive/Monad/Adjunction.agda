------------------------------------------------------------------------
-- The partiality monad's monad instance, defined via an adjunction
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Partiality-monad.Inductive.Monad.Adjunction where

open import Equality.Propositional
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (⊥)

open import Adjunction equality-with-J
open import Bijection equality-with-J using (_↔_)
open import Category equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)
open import Functor equality-with-J
open import H-level equality-with-J hiding (Type)
open import H-level.Closure equality-with-J

open import Partiality-monad.Inductive as PI
  using (_⊥; partiality-algebra; initial)
open import Partiality-monad.Inductive.Eliminators
import Partiality-monad.Inductive.Monad as PM
import Partiality-monad.Inductive.Omega-continuous as PO
open import Partiality-monad.Inductive.Partiality-algebra as PA
  hiding (id; _∘_)
import Partiality-monad.Inductive.Partiality-algebra.Properties as PAP

-- A forgetful functor from partiality algebras to sets.

Forget : ∀ {a p q} {A : Set a} →
         PA.precategory p q A ⇨ precategory-Set p ext
functor Forget =
    (λ P → Type P , Type-is-set P)
  , Morphism.function
  , refl
  , refl
  where
  open Partiality-algebra

-- The precategory of pointed ω-cpos.

ω-CPPO : ∀ p q → Precategory (lsuc (p ⊔ q)) (p ⊔ q)
ω-CPPO p q = PA.precategory p q ⊥₀

-- Pointed ω-cpos.

ω-cppo : ∀ p q → Set (lsuc (p ⊔ q))
ω-cppo p q = Partiality-algebra p q ⊥₀

-- If there is a function from B to the carrier of P, then P
-- can be converted to a partiality algebra over B.

convert : ∀ {a b p q} {A : Set a} {B : Set b} →
          (P : Partiality-algebra p q A) →
          (B → Partiality-algebra.Type P) →
          Partiality-algebra p q B
convert P f = record
  { Type               = Type
  ; _⊑_                = _⊑_
  ; never              = never
  ; now                = f
  ; ⨆                  = ⨆
  ; antisymmetry       = antisymmetry
  ; Type-UIP-unused    = Type-UIP-unused
  ; ⊑-refl             = ⊑-refl
  ; ⊑-trans            = ⊑-trans
  ; never⊑             = never⊑
  ; upper-bound        = upper-bound
  ; least-upper-bound  = least-upper-bound
  ; ⊑-proof-irrelevant = ⊑-proof-irrelevant
  }
  where
  open Partiality-algebra P

-- A lemma that removes convert from certain types.

drop-convert :
  ∀ {a p q p′ q′} {A : Set a} {X : ω-cppo p q} {Y : ω-cppo p′ q′}
    {f : A → _} {g : A → _} →
  Morphism (convert X f) (convert Y g) → Morphism X Y
drop-convert m = record
  { function     = function
  ; monotone     = monotone
  ; strict       = strict
  ; now-to-now   = λ x → ⊥-elim x
  ; ω-continuous = ω-continuous
  }
  where
  open Morphism m

-- Converts partiality algebras to ω-cppos.

drop-now : ∀ {a p q} {A : Set a} →
           Partiality-algebra p q A → ω-cppo p q
drop-now P = convert P ⊥-elim

-- The function drop-now does not modify ω-cppos.

drop-now-constant :
  ∀ {p q} {P : ω-cppo p q} →
  drop-now P ≡ P
drop-now-constant =
  cong (λ now → record { now = now }) (ext λ x → ⊥-elim x)

-- Converts types to ω-cppos.

Partial⊚ : ∀ {ℓ} → Set ℓ → ω-cppo ℓ ℓ
Partial⊚ = drop-now ∘ partiality-algebra

private

  -- A lemma.

  Partial⊙′ :
    let open Partiality-algebra; open Morphism in

    ∀ {a b p q} {A : Set a} {B : Set b}
    (P : Partiality-algebra p q B) →
    (f : A → Type P) →
    ∃ λ (m : Morphism (Partial⊚ A) (drop-now P)) →
      (∀ x → function m (PI.now x) ≡ now (convert P f) x)
        ×
      (∀ m′ → (∀ x → function m′ (PI.now x) ≡ now (convert P f) x) →
              m ≡ m′)
  Partial⊙′ {A = A} P f = m′ , PI.⊥-rec-now _ , lemma
    where
    P′ : Partiality-algebra _ _ A
    P′ = convert P f

    m : Morphism (partiality-algebra A) P′
    m = proj₁ (initial P′)

    m′ : Morphism (Partial⊚ A) (drop-now P)
    m′ = drop-convert m

    abstract

      lemma :
        ∀ m″ →
        (∀ x → Morphism.function m″ (PI.now x) ≡
               Partiality-algebra.now P′ x) →
        m′ ≡ m″
      lemma m″ hyp = _↔_.to equality-characterisation-Morphism (
        function m′  ≡⟨⟩
        function m   ≡⟨ cong function (proj₂ (initial P′) record
                                         { function     = function m″
                                         ; monotone     = monotone m″
                                         ; strict       = strict m″
                                         ; now-to-now   = hyp
                                         ; ω-continuous =
                                             ω-continuous m″
                                         }) ⟩∎
        function m″  ∎)
        where
        open Morphism

-- Lifts functions between types to morphisms between the
-- corresponding ω-cppos.

Partial⊙ :
  ∀ {a b} {A : Set a} {B : Set b} →
  (A → B) → Morphism (Partial⊚ A) (Partial⊚ B)
Partial⊙ f = proj₁ (Partial⊙′ (partiality-algebra _) (PI.now ∘ f))

-- Partial⊙ f is the unique morphism (of the given type) mapping
-- PI.now x to PI.now (f x) (for all x).

Partial⊙-now :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {x} →
  Morphism.function (Partial⊙ f) (PI.now x) ≡ PI.now (f x)
Partial⊙-now = proj₁ (proj₂ (Partial⊙′ (partiality-algebra _) _)) _

Partial⊙-unique :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {m} →
    (∀ x → Morphism.function m (PI.now x) ≡ PI.now (f x)) →
  Partial⊙ f ≡ m
Partial⊙-unique = proj₂ (proj₂ (Partial⊙′ (partiality-algebra _) _)) _

-- A functor that maps a set A to A ⊥.

Partial : ∀ {ℓ} → precategory-Set ℓ ext ⇨ ω-CPPO ℓ ℓ
_⇨_.functor (Partial {ℓ}) =
    Partial⊚ ∘ proj₁
  , Partial⊙
  , L.lemma₁
  , L.lemma₂
  where
  open Morphism

  module L where
   abstract

    lemma₁ : {A : Set ℓ} → Partial⊙ (id {A = A}) ≡ PA.id
    lemma₁ = Partial⊙-unique λ _ → refl

    lemma₂ : {A B C : Set ℓ} {f : A → B} {g : B → C} →
             Partial⊙ (g ∘ f) ≡ Partial⊙ g PA.∘ Partial⊙ f
    lemma₂ {f = f} {g} = Partial⊙-unique λ x →
      function (Partial⊙ g PA.∘ Partial⊙ f) (PI.now x)  ≡⟨ cong (function (Partial⊙ g)) $ PI.⊥-rec-now _ _ ⟩
      function (Partial⊙ g) (PI.now (f x))              ≡⟨ PI.⊥-rec-now _ _ ⟩∎
      PI.now (g (f x))                                  ∎

-- Partial is a left adjoint of Forget.

Partial⊣Forget : ∀ {ℓ} → Partial {ℓ = ℓ} ⊣ Forget
Partial⊣Forget {ℓ} =
    η
  , ε
  , (λ {X} →
       let P = Partial⊚ (proj₁ X) in
       _↔_.to equality-characterisation-Morphism $ ext $
       ⊥-rec-⊥ record
         { pe = fun P (function (Partial⊙ PI.now) PI.never)  ≡⟨ cong (fun P) $ strict (Partial⊙ PI.now) ⟩
                fun P PI.never                               ≡⟨ strict (m P _) ⟩∎
                PI.never                                     ∎
         ; po = λ x →
                  fun P (function (Partial⊙ PI.now) (PI.now x))  ≡⟨ cong (fun P) Partial⊙-now ⟩
                  fun P (PI.now (PI.now x))                      ≡⟨ fun-now P ⟩∎
                  PI.now x                                       ∎
         ; pl = λ s hyp →
                  fun P (function (Partial⊙ PI.now) (PI.⨆ s))  ≡⟨ cong (fun P) $ ω-continuous (Partial⊙ PI.now) _ ⟩
                  fun P (PI.⨆ _)                               ≡⟨ ω-continuous (m P _) _ ⟩
                  PI.⨆ _                                       ≡⟨ cong PI.⨆ $ _↔_.to PI.equality-characterisation-increasing hyp ⟩∎
                  PI.⨆ s                                       ∎
         ; pp = λ _ → PI.⊥-is-set _ _
         })
  , (λ {X} → ext λ x →
       fun X (PI.now x)  ≡⟨ fun-now X ⟩∎
       x                 ∎)
  where
  open Morphism {q₂ = ℓ}
  open PAP
  open Partiality-algebra

  η : id⇨ ⇾ Forget ∙⇨ Partial
  _⇾_.natural-transformation η =
      PI.now
    , (λ {X Y f} → ext λ x →
         PI.⊥-rec (record { po = PI.now ∘ f }) (PI.now x)  ≡⟨ PI.⊥-rec-now _ x ⟩∎
         PI.now (f x)                                      ∎)

  m : (X : ω-cppo ℓ ℓ) {A : Set ℓ} → (A → Type X) →
      Morphism (Partial⊚ A) X
  m X {A} =
    (A → Type X)                        ↝⟨ proj₁ ∘ Partial⊙′ X ⟩
    Morphism (Partial⊚ A) (drop-now X)  ↝⟨ drop-convert ⟩□
    Morphism (Partial⊚ A) X             □

  fun : (X : ω-cppo ℓ ℓ) → Type X ⊥ → Type X
  fun X = function (m X id)

  fun-now : ∀ (X : ω-cppo ℓ ℓ) {x} → fun X (PI.now x) ≡ x
  fun-now X = proj₁ (proj₂ (Partial⊙′ X _)) _

  fun-unique :
    (X : ω-cppo ℓ ℓ) (m′ : Morphism (Partial⊚ (Type X)) X) →
    (∀ x → function m′ (PI.now x) ≡ x) →
    fun X ≡ function m′
  fun-unique X m′ hyp =
    cong function $ proj₂ (proj₂ (Partial⊙′ X _)) (drop-convert m′) hyp

  ε : Partial ∙⇨ Forget ⇾ id⇨
  _⇾_.natural-transformation ε =
      (λ {X} → m X id)
    , (λ {X Y f} →
         let m′ = (Partial ∙⇨ Forget) ⊙ f in
         _↔_.to equality-characterisation-Morphism $ ext $
         ⊥-rec-⊥ record
           { pe = function f (fun X PI.never)   ≡⟨ cong (function f) (strict (m X _)) ⟩
                  function f (never X)          ≡⟨ strict f ⟩
                  never Y                       ≡⟨ sym $ strict (m Y _) ⟩
                  fun Y PI.never                ≡⟨ cong (fun Y) $ sym $ strict m′ ⟩∎
                  fun Y (function m′ PI.never)  ∎
           ; po = λ x →
                    function f (fun X (PI.now x))   ≡⟨ cong (function f) (fun-now X) ⟩
                    function f x                    ≡⟨ sym $ fun-now Y ⟩
                    fun Y (PI.now (function f x))   ≡⟨ cong (fun Y) $ sym Partial⊙-now ⟩∎
                    fun Y (function m′ (PI.now x))  ∎
           ; pl = λ s hyp →
                    function f (fun X (PI.⨆ s))   ≡⟨ cong (function f) (ω-continuous (m X _) _) ⟩
                    function f (⨆ X _)            ≡⟨ ω-continuous f _ ⟩
                    ⨆ Y _                         ≡⟨ cong (⨆ Y) $ _↔_.to (equality-characterisation-increasing Y) hyp ⟩
                    ⨆ Y _                         ≡⟨ sym $ ω-continuous (m Y _) _ ⟩
                    fun Y (PI.⨆ _)                ≡⟨ cong (fun Y) $ sym $ ω-continuous m′ _ ⟩∎
                    fun Y (function m′ (PI.⨆ s))  ∎
           ; pp = λ _ → Type-is-set Y _ _
           })

-- Thus we get that the partiality monad is a monad.

Partiality-monad : ∀ {ℓ} → Monad (precategory-Set ℓ ext)
Partiality-monad = adjunction→monad (Partial , Forget , Partial⊣Forget)

private

  -- The object part of the monad's functor really does correspond to
  -- the partiality monad.

  object-part-of-functor-correct :
    ∀ {a} {A : SET a} →
    proj₁ (proj₁ Partiality-monad ⊚ A) ≡ proj₁ A ⊥
  object-part-of-functor-correct = refl

  -- The definition of "map" obtained here matches the explicit
  -- definition in Partiality-monad.Inductive.Monad.

  map-correct :
    ∀ {ℓ} {A B : SET ℓ} {f : proj₁ A → proj₁ B} →
    _⊙_ (proj₁ Partiality-monad) {X = A} {Y = B} f ≡
    PO.[_⊥→_⊥].function (PM.map f)
  map-correct = refl

  -- The definition of "return" is the expected one.

  return-correct :
    ∀ {a} {A : SET a} →
    _⇾_.transformation (proj₁ (proj₂ Partiality-monad)) {X = A} ≡ PI.now
  return-correct = refl

  -- The definition of "join" obtained here matches the explicit
  -- definition in Partiality-monad.Inductive.Monad.

  join-correct :
    ∀ {a} {A : SET a} →
    _⇾_.transformation
      (proj₁ (proj₂ (proj₂ Partiality-monad))) {X = A} ≡
    PM.join
  join-correct = refl
