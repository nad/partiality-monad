------------------------------------------------------------------------
-- Partiality algebras
------------------------------------------------------------------------

{-# OPTIONS --without-K --rewriting #-}

-- The code below uses ideas and concepts from "Inductive types in
-- homotopy type theory" by Awodey, Gambino and Sojakova, and
-- "Inductive Types in Homotopy Type Theory" by Sojakova.

module Partiality-monad.Inductive.Partiality-algebra where

open import Equality.Propositional
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (id) renaming (_∘_ to _⊚_)

open import Bijection equality-with-J using (_↔_)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J as H-level hiding (Type)
open import H-level.Closure equality-with-J
open import Surjection equality-with-J using (_↠_)

import Partiality-monad.Inductive as I
import Partiality-monad.Inductive.Eliminators as E
import Partiality-monad.Inductive.Properties as IP

-- Partiality algebras.

record Partiality-algebra {a} p q (A : Set a) :
                          Set (a ⊔ lsuc (p ⊔ q)) where

  -- A type and a binary relation on that type.

  field
    Type : Set p
    _⊑_  : Type → Type → Set q

  -- Increasing sequences.

  Increasing-sequence : Set (p ⊔ q)
  Increasing-sequence = ∃ λ (f : ℕ → Type) → ∀ n → f n ⊑ f (suc n)

  -- Projection functions for Increasing-sequence.

  infix 30 _[_]

  _[_] : Increasing-sequence → ℕ → Type
  _[_] s n = proj₁ s n

  increasing : (s : Increasing-sequence) →
               ∀ n → (s [ n ]) ⊑ (s [ suc n ])
  increasing = proj₂

  -- Upper bounds.

  Is-upper-bound : Increasing-sequence → Type → Set q
  Is-upper-bound s x = ∀ n → (s [ n ]) ⊑ x

  -- Fields corresponding to the constructors of I._⊥ and I._⊑_.

  field
    never              : Type
    now                : A → Type
    ⨆                  : Increasing-sequence → Type
    antisymmetry       : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
    ≡-proof-irrelevant : {x y : Type} → Proof-irrelevant (x ≡ y)
    ⊑-refl             : ∀ x → x ⊑ x
    ⊑-trans            : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
    never⊑             : ∀ x → never ⊑ x
    upper-bound        : ∀ s → Is-upper-bound s (⨆ s)
    least-upper-bound  : ∀ s ub → Is-upper-bound s ub → ⨆ s ⊑ ub
    ⊑-proof-irrelevant : ∀ {x y} → Proof-irrelevant (x ⊑ y)

  -- _⊑_ is propositional.

  ⊑-propositional : ∀ {x y} → Is-proposition (x ⊑ y)
  ⊑-propositional =
    _⇔_.from propositional⇔irrelevant ⊑-proof-irrelevant

  private

    -- A lemma.

    Type-is-set-and-equality-characterisation : Is-set Type × _
    Type-is-set-and-equality-characterisation =
      Eq.propositional-identity≃≡
        (λ x y → x ⊑ y × y ⊑ x)
        (λ _ _ → ×-closure 1 ⊑-propositional ⊑-propositional)
        (λ x → ⊑-refl x , ⊑-refl x)
        (λ x y → uncurry {B = λ _ → y ⊑ x} antisymmetry)

  -- Type is a set. (This lemma is analogous to Theorem 11.3.9 in
  -- "Homotopy Type Theory: Univalent Foundations of Mathematics"
  -- (first edition).)

  Type-is-set : Is-set Type
  Type-is-set = proj₁ Type-is-set-and-equality-characterisation

  -- Equality characterisation lemma for Type.

  equality-characterisation-Type :
    ∀ {x y} → (x ⊑ y × y ⊑ x) ≃ (x ≡ y)
  equality-characterisation-Type =
    proj₂ Type-is-set-and-equality-characterisation ext

  -- Equality characterisation lemma for increasing sequences.

  equality-characterisation-increasing :
    ∀ {s₁ s₂} → (∀ n → s₁ [ n ] ≡ s₂ [ n ]) ↔ s₁ ≡ s₂
  equality-characterisation-increasing {s₁} {s₂} =
    (∀ n → s₁ [ n ] ≡ s₂ [ n ])  ↔⟨ Eq.extensionality-isomorphism ext ⟩
    proj₁ s₁ ≡ proj₁ s₂          ↝⟨ ignore-propositional-component
                                      (Π-closure ext 1 λ _ →
                                       ⊑-propositional) ⟩□
    s₁ ≡ s₂                      □

-- The partiality monad is a family of partiality algebras.

Partiality-monad : ∀ {a} (A : Set a) → Partiality-algebra a a A
Partiality-monad A = record
  { Type               = A I.⊥
  ; _⊑_                = I._⊑_
  ; never              = I.never
  ; now                = I.now
  ; ⨆                  = I.⨆
  ; antisymmetry       = I.antisymmetry
  ; ≡-proof-irrelevant = _⇔_.to set⇔UIP IP.⊥-is-set
  ; ⊑-refl             = I.⊑-refl
  ; ⊑-trans            = I.⊑-trans
  ; never⊑             = I.never⊑
  ; upper-bound        = I.upper-bound
  ; least-upper-bound  = I.least-upper-bound
  ; ⊑-proof-irrelevant = I.⊑-proof-irrelevant
  }

-- Partiality algebra morphisms.

record Morphism {a p₁ p₂ q₁ q₂} {A : Set a}
                (P₁ : Partiality-algebra p₁ q₁ A)
                (P₂ : Partiality-algebra p₂ q₂ A) :
                Set (a ⊔ p₁ ⊔ p₂ ⊔ q₁ ⊔ q₂) where

  private
    module P₁ = Partiality-algebra P₁
    module P₂ = Partiality-algebra P₂

  field
    function     : P₁.Type → P₂.Type
    monotone     : ∀ {x y} → x P₁.⊑ y → function x P₂.⊑ function y

  sequence-function : P₁.Increasing-sequence → P₂.Increasing-sequence
  sequence-function = Σ-map (function ⊚_) (monotone ⊚_)

  field
    strict       : function P₁.never ≡ P₂.never
    now-to-now   : ∀ x → function (P₁.now x) ≡ P₂.now x
    ω-continuous : ∀ s → function (P₁.⨆ s) ≡ P₂.⨆ (sequence-function s)

-- An identity morphism.

id : ∀ {a p q} {A : Set a} {P : Partiality-algebra p q A} → Morphism P P
id = record
  { function     = Prelude.id
  ; monotone     = Prelude.id
  ; strict       = refl
  ; now-to-now   = λ _ → refl
  ; ω-continuous = λ _ → refl
  }

-- Composition of morphisms.

_∘_ : ∀ {a p₁ p₂ p₃ q₁ q₂ q₃} {A : Set a}
        {P₁ : Partiality-algebra p₁ q₁ A}
        {P₂ : Partiality-algebra p₂ q₂ A}
        {P₃ : Partiality-algebra p₃ q₃ A} →
      Morphism P₂ P₃ → Morphism P₁ P₂ → Morphism P₁ P₃
_∘_ {P₁ = P₁} {P₂} {P₃} m₁ m₂ = record
  { function     = function m₁ ⊚ function m₂
  ; monotone     = monotone m₁ ⊚ monotone m₂
  ; strict       = function m₁ (function m₂ (never P₁))  ≡⟨ cong (function m₁) (strict m₂) ⟩
                   function m₁ (never P₂)                ≡⟨ strict m₁ ⟩∎
                   never P₃                              ∎
  ; now-to-now   = λ x →
                     function m₁ (function m₂ (now P₁ x))  ≡⟨ cong (function m₁) (now-to-now m₂ x) ⟩
                     function m₁ (now P₂ x)                ≡⟨ now-to-now m₁ x ⟩∎
                     now P₃ x                              ∎
  ; ω-continuous = λ s →
      function m₁ (function m₂ (⨆ P₁ s))                    ≡⟨ cong (function m₁) (ω-continuous m₂ s) ⟩
      function m₁ (⨆ P₂ (sequence-function m₂ s))           ≡⟨ ω-continuous m₁ (sequence-function m₂ s) ⟩∎
      ⨆ P₃ (sequence-function m₁ (sequence-function m₂ s))  ∎
  }
  where
  open Morphism
  open Partiality-algebra

-- The statement that a given partiality algebra is homotopy-initial.

Initial : ∀ {a p q} p′ q′ {A : Set a} → Partiality-algebra p q A →
          Set (a ⊔ p ⊔ q ⊔ lsuc (p′ ⊔ q′))
Initial p′ q′ {A} P =
  (P′ : Partiality-algebra p′ q′ A) → Contractible (Morphism P P′)

-- Partiality-monad A is an initial partiality algebra (at all sizes).

partiality-monad-initial :
  ∀ {a p q} {A : Set a} → Initial p q (Partiality-monad A)
partiality-monad-initial {A = A} P = morphism , unique
  where
  module P = Partiality-algebra P

  args : E.Rec-args-nd A P.Type P._⊑_
  args = record
    { pe = P.never
    ; po = P.now
    ; pl = λ _ → P.⨆
    ; pa = λ _ _ → P.antisymmetry
    ; ps = P.Type-is-set
    ; qr = λ _ → P.⊑-refl
    ; qt = λ _ _ _ _ _ → P.⊑-trans
    ; qe = λ _ → P.never⊑
    ; qu = λ _ → P.upper-bound
    ; ql = λ _ _ _ → P.least-upper-bound
    ; qp = λ _ _ → _⇔_.from propositional⇔irrelevant
                     P.⊑-proof-irrelevant
    }

  morphism : Morphism (Partiality-monad A) P
  morphism = record
    { function     = E.⊥-rec-nd args
    ; monotone     = E.⊑-rec-nd args
    ; strict       = refl
    ; now-to-now   = λ _ → refl
    ; ω-continuous = λ _ → refl
    }

  open Morphism

  function-unique : (f : Morphism (Partiality-monad A) P) →
                    E.⊥-rec-nd args ≡ function f
  function-unique f = sym $ ext $ E.⊥-rec-⊥ (record
    { pe = strict f
    ; po = now-to-now f
    ; pl = λ s hyp →
             function f (I.⨆ s)           ≡⟨ ω-continuous f s ⟩
             P.⨆ (sequence-function f s)  ≡⟨ cong P.⨆ $ _↔_.to P.equality-characterisation-increasing hyp ⟩∎
             P.⨆ (E.inc-rec-nd args s)    ∎
    ; pp = λ _ → P.Type-is-set _ _
    })

  unique : ∀ f → morphism ≡ f
  unique f = cong rearrange $ Σ-≡,≡→≡
    (function-unique f)
    (_⇔_.to propositional⇔irrelevant
       (Σ-closure 1
          (implicit-Π-closure ext 1 λ _ →
           implicit-Π-closure ext 1 λ _ →
           Π-closure ext 1 λ _ →
           P.⊑-propositional) λ _ →
        ×-closure 1
          (P.Type-is-set _ _) $
        ×-closure 1
          (Π-closure ext 1 λ _ →
           P.Type-is-set _ _) $
        Π-closure ext 1 λ _ →
        P.Type-is-set _ _)
       _ _)
    where
    rearrange :
      (∃ λ (f : A I.⊥ → P.Type) →
       ∃ λ (m : ∀ {x y} → x I.⊑ y → f x P.⊑ f y) →
       f I.never ≡ P.never
         ×
       (∀ x → f (I.now x) ≡ P.now x)
         ×
       (∀ s → f (I.⨆ s) ≡
              P.⨆ (Σ-map (f ⊚_) (m ⊚_) s))) →
      Morphism (Partiality-monad A) P
    rearrange (f , m , s , n , ω) = record
      { function     = f
      ; monotone     = m
      ; strict       = s
      ; now-to-now   = n
      ; ω-continuous = ω
      }

-- If PA is an initial partiality algebra (with certain size indices),
-- then an eliminator like the one for the partiality monad
-- (eliminating into things of the corresponding sizes) can be defined
-- for PA.

module Eliminator-for-initial-partiality-algebra
  {a p q} {A : Set a}
  (PA : Partiality-algebra p q A)
  (initial : Initial p q PA)
  where

  open Partiality-algebra PA

  -- Predicate transformer related to increasing sequences.

  Inc : (P : Type → Set p)
        (Q : ∀ {x y} → P x → P y → x ⊑ y → Set q) →
        Increasing-sequence → Set (p ⊔ q)
  Inc P Q s =
    ∃ λ (p : ∀ n → P (s [ n ])) →
      ∀ n → Q (p n) (p (suc n)) (increasing s n)

  -- Record wrapping up the eliminators' arguments.

  record Rec-args
           (P : Type → Set p)
           (Q : ∀ {x y} → P x → P y → x ⊑ y → Set q) :
           Set (a ⊔ p ⊔ q) where
    field
      pe : P never
      po : ∀ x → P (now x)
      pl : ∀ s (pq : Inc P Q s) → P (⨆ s)
      pa : ∀ {x y} (x⊑y : x ⊑ y) (x⊒y : y ⊑ x)
           (p-x : P x) (p-y : P y)
           (q-x⊑y : Q p-x p-y x⊑y) (q-x⊒y : Q p-y p-x x⊒y) →
           subst P (antisymmetry x⊑y x⊒y) p-x ≡ p-y
      pp : ∀ {x} {p₁ p₂ : P x} → Proof-irrelevant (p₁ ≡ p₂)
      qr : ∀ x (p : P x) → Q p p (⊑-refl x)
      qt : ∀ {x y z} (x⊑y : x ⊑ y) (y⊑z : y ⊑ z) →
           (px : P x) (py : P y) (pz : P z) →
           Q px py x⊑y → Q py pz y⊑z → Q px pz (⊑-trans x⊑y y⊑z)
      qe : ∀ x (p : P x) → Q pe p (never⊑ x)
      qu : ∀ s (pq : Inc P Q s) n →
           Q (proj₁ pq n) (pl s pq) (upper-bound s n)
      ql : ∀ s ub is-ub (pq : Inc P Q s) (pu : P ub)
           (qu : ∀ n → Q (proj₁ pq n) pu (is-ub n)) →
           Q (pl s pq) pu (least-upper-bound s ub is-ub)
      qp : ∀ {x y} (p-x : P x) (p-y : P y) (x⊑y : x ⊑ y) →
           Proof-irrelevant (Q p-x p-y x⊑y)

  -- The eliminators.

  module _
    {P : Type → Set p}
    {Q : ∀ {x y} → P x → P y → x ⊑ y → Set q}
    (args : Rec-args P Q)
    where

    open Rec-args args

    private

      -- A partiality algebra with ∃ P as the carrier type.

      ∃PA : Partiality-algebra p q A
      ∃PA = record
        { Type               = ∃ P
        ; _⊑_                = λ { (_ , p) (_ , q) → ∃ (Q p q) }
        ; never              = never , pe
        ; now                = λ x → now x , po x
        ; ⨆                  = λ s → ⨆ (Σ-map (proj₁ ⊚_) (proj₁ ⊚_) s)
                                   , pl _ ( proj₂ ⊚ proj₁ s
                                          , proj₂ ⊚ proj₂ s
                                          )
        ; antisymmetry       = λ { {x = (x , p)} {y = (y , q)}
                                   (x⊑y , Qx⊑y) (y⊑x , Qy⊑x) →
                                   Σ-≡,≡→≡
                                     (antisymmetry x⊑y y⊑x)
                                     (pa x⊑y y⊑x p q Qx⊑y Qy⊑x)
                                 }
        ; ≡-proof-irrelevant = _⇔_.to propositional⇔irrelevant
                                 (Σ-closure 2
                                    Type-is-set
                                    (λ _ → _⇔_.from set⇔UIP pp)
                                    _ _)
        ; ⊑-refl             = λ _ → _ , qr _ _
        ; ⊑-trans            = Σ-zip ⊑-trans (qt _ _ _ _ _)
        ; never⊑             = λ _ → _ , qe _ _
        ; upper-bound        = λ _ _ → upper-bound _ _ , qu _ _ _
        ; least-upper-bound  = λ _ _ ⊑qs →
                                   least-upper-bound _ _ (proj₁ ⊚ ⊑qs)
                                 , ql _ _ _ _ _ (proj₂ ⊚ ⊑qs)
        ; ⊑-proof-irrelevant = _⇔_.to propositional⇔irrelevant
                                 (Σ-closure 1 ⊑-propositional λ _ →
                                    _⇔_.from propositional⇔irrelevant
                                      (qp _ _ _))
        }

      -- Initiality gives us a morphism from PA to ∃PA.

      eliminator-morphism : Morphism PA ∃PA
      eliminator-morphism = proj₁ (initial ∃PA)

      open Morphism eliminator-morphism

      -- We can construct a morphism from ∃PA to PA directly.

      proj₁-morphism : Morphism ∃PA PA
      proj₁-morphism = record
        { function     = proj₁
        ; monotone     = proj₁
        ; strict       = refl
        ; now-to-now   = λ _ → refl
        ; ω-continuous = λ _ → refl
        }

      -- By composing the two morphisms we get an endomorphism on PA.

      id′ : Morphism PA PA
      id′ = proj₁-morphism ∘ eliminator-morphism

      -- Due to initiality this morphism must be equal to id.

      id′≡id : id′ ≡ id
      id′≡id =
        id′                 ≡⟨ sym $ proj₂ (initial PA) id′ ⟩
        proj₁ (initial PA)  ≡⟨ proj₂ (initial PA) id ⟩∎
        id                  ∎

      -- This provides us with a key lemma used to define the
      -- eliminators.

      lemma : ∀ x → proj₁ (function x) ≡ x
      lemma x = cong (λ m → Morphism.function m x) id′≡id

      -- As an aside this means that there is a split surjection from
      -- ∃ P to Type.

      ↠Type : ∃ P ↠ Type
      ↠Type = record
        { logical-equivalence = record
          { to   = Morphism.function proj₁-morphism
          ; from = function
          }
        ; right-inverse-of = lemma
        }

    -- The eliminators.

    ⊥-rec : ∀ x → P x
    ⊥-rec x =                 $⟨ proj₂ (function x) ⟩
      P (proj₁ (function x))  ↝⟨ subst P (lemma x) ⟩□
      P x                     □

    ⊑-rec : ∀ {x y} (x⊑y : x ⊑ y) → Q (⊥-rec x) (⊥-rec y) x⊑y
    ⊑-rec {x} {y} x⊑y =                                                   $⟨ proj₂ (monotone x⊑y) ⟩
      Q (proj₂ (function x)) (proj₂ (function y)) (proj₁ (monotone x⊑y))  ↝⟨ subst Q′ $
                                                                               Σ-≡,≡→≡ (cong₂ _,_ (lemma x) (lemma y)) (
          subst (λ xy → P (proj₁ xy) × P (proj₂ xy) ×
                        proj₁ xy ⊑ proj₂ xy)
                (cong₂ _,_ (lemma x) (lemma y))
                ( proj₂ (function x)
                , proj₂ (function y)
                , proj₁ (monotone x⊑y)
                )                                                                 ≡⟨ push-subst-, {y≡z = cong₂ _,_ (lemma x) (lemma y)}
                                                                                                  (λ xy → P (proj₁ xy))
                                                                                                  (λ xy → P (proj₂ xy) × proj₁ xy ⊑ proj₂ xy)
                                                                                                  {p = ( proj₂ (function x)
                                                                                                       , proj₂ (function y)
                                                                                                       , proj₁ (monotone x⊑y)
                                                                                                       )} ⟩
          ( subst (λ xy → P (proj₁ xy))
                  (cong₂ _,_ (lemma x) (lemma y))
                  (proj₂ (function x))
          , subst (λ xy → P (proj₂ xy) × proj₁ xy ⊑ proj₂ xy)
                  (cong₂ _,_ (lemma x) (lemma y))
                  ( proj₂ (function y)
                  , proj₁ (monotone x⊑y)
                  )
          )                                                                       ≡⟨ cong₂ _,_
                                                                                       (subst-∘ P proj₁ (cong₂ _,_ (lemma x) (lemma y))
                                                                                                {p = proj₂ (function x)})
                                                                                       (push-subst-, {y≡z = cong₂ _,_ (lemma x) (lemma y)}
                                                                                                     (λ xy → P (proj₂ xy))
                                                                                                     (λ xy → proj₁ xy ⊑ proj₂ xy)
                                                                                                     {p = ( proj₂ (function y)
                                                                                                          , proj₁ (monotone x⊑y)
                                                                                                          )}) ⟩
          ( subst P (cong proj₁ $ cong₂ _,_ (lemma x) (lemma y))
                  (proj₂ (function x))
          , subst (λ xy → P (proj₂ xy))
                  (cong₂ _,_ (lemma x) (lemma y))
                  (proj₂ (function y))
          , subst (λ xy → proj₁ xy ⊑ proj₂ xy)
                  (cong₂ _,_ (lemma x) (lemma y))
                  (proj₁ (monotone x⊑y))
          )                                                                       ≡⟨ cong₂ _,_
                                                                                       (cong (λ p → subst P p (proj₂ (function x))) $
                                                                                          cong-proj₁-cong₂-, (lemma x) (lemma y))
                                                                                       (cong₂ _,_
                                                                                          (subst-∘ P proj₂ (cong₂ _,_ (lemma x) (lemma y))
                                                                                                   {p = proj₂ (function y)})
                                                                                          (_⇔_.to propositional⇔irrelevant
                                                                                             ⊑-propositional
                                                                                             _ _)) ⟩
          ( subst P (lemma x) (proj₂ (function x))
          , subst P (cong proj₂ $ cong₂ _,_ (lemma x) (lemma y))
                  (proj₂ (function y))
          , x⊑y
          )                                                                       ≡⟨ cong (λ p → ⊥-rec x , subst P p (proj₂ (function y)) , x⊑y) $
                                                                                       cong-proj₂-cong₂-, (lemma x) (lemma y) ⟩∎
          (⊥-rec x , ⊥-rec y , x⊑y)                                               ∎) ⟩□

      Q (⊥-rec x) (⊥-rec y) x⊑y                                           □
      where
      Q′ :
        (∃ λ xy → P (proj₁ xy) × P (proj₂ xy) × proj₁ xy ⊑ proj₂ xy) →
        Set q
      Q′ (_ , px , py , x⊑y) = Q px py x⊑y

    inc-rec : ∀ s → Inc P Q s
    inc-rec (s , inc) = ⊥-rec ⊚ s , ⊑-rec ⊚ inc

    -- The eliminators do not compute in the right way, but most of
    -- the corresponding propositional equalities can be proved. (Some
    -- of the computation rules were not type-correct, so casts have
    -- been inserted.)

    private

      -- A lemma.

      ⊥-rec-lemma′ :
        ∀ {a b} {A : Set a} {B : A → Set b} {x y : Σ A B} →
        Is-set A →
        x ≡ y → (p : proj₁ x ≡ proj₁ y) →
        subst B p (proj₂ x) ≡ proj₂ y
      ⊥-rec-lemma′ {B = B} A-set =
        elim (λ {x y} _ → (p : proj₁ x ≡ proj₁ y) →
                          subst B p (proj₂ x) ≡ proj₂ y)
             (λ { (_ , x₂) p →
                  subst B p x₂     ≡⟨ cong (λ p → subst B p _) $
                                        _⇔_.to set⇔UIP A-set p refl ⟩
                  subst B refl x₂  ≡⟨⟩

                  x₂               ∎
                })

      -- A specific instance of the lemma above.

      ⊥-rec-lemma : ∀ {x y} → function x ≡ (x , y) → ⊥-rec x ≡ y
      ⊥-rec-lemma {x} {y} eq =
        ⊥-rec x                                 ≡⟨⟩
        subst P (lemma x) (proj₂ (function x))  ≡⟨ ⊥-rec-lemma′ Type-is-set eq (lemma x) ⟩∎
        y                                       ∎

    ⊥-rec-never : ⊥-rec never ≡ pe
    ⊥-rec-never = ⊥-rec-lemma strict

    ⊥-rec-now : ∀ x → ⊥-rec (now x) ≡ po x
    ⊥-rec-now x = ⊥-rec-lemma (now-to-now x)

    ⊥-rec-⨆ : ∀ s → ⊥-rec (⨆ s) ≡ pl s (inc-rec s)
    ⊥-rec-⨆ s = ⊥-rec-lemma
      (function (⨆ s)                                           ≡⟨ ω-continuous s ⟩

       ⨆ (Σ-map (proj₁ ⊚_) (proj₁ ⊚_) (sequence-function s)) ,
       pl _ ( proj₂ ⊚ proj₁ (sequence-function s)
            , proj₂ ⊚ proj₂ (sequence-function s)
            )                                                   ≡⟨⟩

       ⨆ ( proj₁ ⊚ function ⊚ proj₁ s
         , proj₁ ⊚ monotone ⊚ proj₂ s
         ) ,
       pl _ ( proj₂ ⊚ function ⊚ proj₁ s
            , proj₂ ⊚ monotone ⊚ proj₂ s
            )                                                   ≡⟨ Σ-≡,≡→≡ (cong ⨆ lemma₁) lemma₂ ⟩

       ⨆ s , pl s ( ⊥-rec ⊚ proj₁ s
                  , ⊑-rec ⊚ proj₂ s
                  )                                             ≡⟨⟩

       ⨆ s , pl s (inc-rec s)                                   ∎)
       where
       lemma₁ =
         ( proj₁ ⊚ function ⊚ proj₁ s
         , proj₁ ⊚ monotone ⊚ proj₂ s
         )                             ≡⟨ _↔_.to equality-characterisation-increasing (λ n →
                                            lemma (s [ n ])) ⟩∎
         s                             ∎

       lemma₂ =
         subst P (cong ⨆ lemma₁)
           (pl _ ( proj₂ ⊚ function ⊚ proj₁ s
                 , proj₂ ⊚ monotone ⊚ proj₂ s
                 ))                                                 ≡⟨ sym $ subst-∘ P ⨆ lemma₁ ⟩

         subst (P ⊚ ⨆) lemma₁
           (pl _ ( proj₂ ⊚ function ⊚ proj₁ s
                 , proj₂ ⊚ monotone ⊚ proj₂ s
                 ))                                                 ≡⟨ elim
                                                                         (λ {s′ s} eq → ∀ {i′ i} →
                                                                                        subst (λ s → ∀ n → P (s [ n ])) eq (proj₁ i′) ≡ proj₁ i →
                                                                                        subst (P ⊚ ⨆) eq (pl s′ i′) ≡ pl s i)
                                                                         (λ s {i′ i} eq →
                                                                            pl s i′  ≡⟨ cong (pl s) (Σ-≡,≡→≡ eq (ext λ _ → qp _ _ _ _ _)) ⟩∎
                                                                            pl s i   ∎)
                                                                         lemma₁
                                                                         (ext λ n →
             let lemma₃ =
                   cong _[ n ] lemma₁                                       ≡⟨ sym $ cong-∘ (_$ n) proj₁ lemma₁ ⟩

                   cong (_$ n) (cong proj₁ lemma₁)                          ≡⟨ cong (cong (_$ n)) $
                                                                                 proj₁-Σ-≡,≡→≡ (Eq.good-ext ext (lemma ⊚ proj₁ s)) _ ⟩
                   cong (_$ n) (Eq.good-ext ext (lemma ⊚ proj₁ s))          ≡⟨ Eq.cong-good-ext ext (lemma ⊚ proj₁ s) ⟩∎

                   lemma (s [ n ])                                          ∎
             in
             subst (λ s → ∀ n → P (s [ n ])) lemma₁
                   (proj₂ ⊚ function ⊚ proj₁ s) n                           ≡⟨ sym $ push-subst-application lemma₁ (λ n s → P (s [ n ])) ⟩

             subst (λ s → P (s [ n ])) lemma₁
                   (proj₂ (function (s [ n ])))                             ≡⟨ subst-∘ P _[ n ] lemma₁ ⟩

             subst P (cong _[ n ] lemma₁)
                   (proj₂ (function (s [ n ])))                             ≡⟨ cong (λ eq → subst P eq (proj₂ (function (s [ n ])))) lemma₃ ⟩∎

             subst P (lemma (s [ n ]))
                   (proj₂ (function (s [ n ])))                             ∎) ⟩

         pl s ( (λ n → subst P (lemma (s [ n ]))
                             (proj₂ (function (s [ n ]))))
              , ⊑-rec ⊚ proj₂ s
              )                                                     ≡⟨⟩

         pl s ( ⊥-rec ⊚ proj₁ s
              , ⊑-rec ⊚ proj₂ s
              )                                                     ∎

    ⊥-rec-antisymmetry :
      ∀ {x y} (x⊑y : x ⊑ y) (x⊒y : y ⊑ x) →
      dependent-cong ⊥-rec (antisymmetry x⊑y x⊒y) ≡
      pa x⊑y x⊒y (⊥-rec x) (⊥-rec y) (⊑-rec x⊑y) (⊑-rec x⊒y)
    ⊥-rec-antisymmetry _ _ = pp _ _

    ⊑-rec-⊑-refl : ∀ x → ⊑-rec (⊑-refl x) ≡ qr x (⊥-rec x)
    ⊑-rec-⊑-refl _ = qp _ _ _ _ _

    ⊑-rec-⊑-trans :
      ∀ {x y z} (x⊑y : x ⊑ y) (y⊑z : y ⊑ z) →
      ⊑-rec (⊑-trans x⊑y y⊑z) ≡
      qt x⊑y y⊑z
         (⊥-rec x) (⊥-rec y) (⊥-rec z)
         (⊑-rec x⊑y) (⊑-rec y⊑z)
    ⊑-rec-⊑-trans _ _ = qp _ _ _ _ _

    ⊑-rec-never⊑ :
      ∀ x →
      subst (λ p → Q p (⊥-rec x) _) ⊥-rec-never (⊑-rec (never⊑ x)) ≡
      qe x (⊥-rec x)
    ⊑-rec-never⊑ _ = qp _ _ _ _ _

    ⊑-rec-upper-bound :
      ∀ s n →
      subst (λ p → Q (⊥-rec (s [ n ])) p (upper-bound s n))
            (⊥-rec-⨆ s)
            (⊑-rec (upper-bound s n)) ≡
      qu s (inc-rec s) n
    ⊑-rec-upper-bound _ _ = qp _ _ _ _ _

    ⊑-rec-least-upper-bound :
      ∀ s ub is-ub →
      subst (λ x → Q x _ _) (⊥-rec-⨆ s)
            (⊑-rec (least-upper-bound s ub is-ub)) ≡
      ql s ub is-ub
         (inc-rec s)
         (⊥-rec ub)
         (λ n → ⊑-rec (is-ub n))
    ⊑-rec-least-upper-bound _ _ _ = qp _ _ _ _ _
