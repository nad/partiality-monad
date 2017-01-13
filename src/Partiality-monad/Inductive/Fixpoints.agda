------------------------------------------------------------------------
-- Fixpoint combinators
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Partiality-monad.Inductive.Fixpoints where

open import Equality.Propositional
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (⊥; head; tail)

open import Bijection equality-with-J using (_↔_)
import Equivalence equality-with-J as Eq
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Monad equality-with-J
open import Univalence-axiom equality-with-J

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Monad
open import Partiality-monad.Inductive.Monotone using ([_⊥→_⊥]⊑)
open import Partiality-monad.Inductive.Omega-continuous
open import Partiality-monad.Inductive.Partiality-algebra
  using (Partiality-algebra)
import Partiality-monad.Inductive.Partiality-algebra.Fixpoints as PAF
open import Partiality-monad.Inductive.Partiality-algebra.Monotone
open import
  Partiality-monad.Inductive.Partiality-algebra.Omega-continuous
open import Partiality-monad.Inductive.Partiality-algebra.Pi as Pi
  hiding (at)

------------------------------------------------------------------------
-- The fixpoint combinator machinery instantiated with the partiality
-- monad

module _ {a} {A : Set a} where

  open PAF.Fix {P = partiality-algebra A} public
  open [_⊥→_⊥]

  -- A variant of fix.

  fix′ : (A → A ⊥) → A ⊥
  fix′ f = fix (monotone-function (f ∗))

  -- This variant also produces a kind of least fixpoint.

  fix′-is-fixpoint-combinator :
    (f : A → A ⊥) →
    fix′ f ≡ fix′ f >>= f
  fix′-is-fixpoint-combinator f =
    fix′ f                               ≡⟨⟩
    fix (monotone-function (f ∗))        ≡⟨ fix-is-fixpoint-combinator (f ∗) ⟩∎
    fix (monotone-function (f ∗)) >>= f  ∎

  fix′-is-least :
    (f : A → A ⊥) →
    ∀ x → x >>= f ⊑ x → fix′ f ⊑ x
  fix′-is-least f = fix-is-least (monotone-function (f ∗))

  -- Taking steps that are "twice as large" does not affect the end
  -- result.

  fix′-∘ : (f : A → A ⊥) → fix′ (λ x → f x >>= f) ≡ fix′ f
  fix′-∘ f =
    fix′ (λ x → f x >>= f)                                    ≡⟨⟩

    fix (monotone-function ((λ x → f x >>= f) ∗))             ≡⟨ cong fix (_↔_.to equality-characterisation-monotone λ x →

        (x >>= λ y → f y >>= f)                                    ≡⟨ associativity x f f ⟩∎
        x >>= f >>= f                                              ∎) ⟩

    fix (monotone-function (f ∗) ∘⊑ monotone-function (f ∗))  ≡⟨ fix-∘ (monotone-function (f ∗)) ⟩∎

    fix′ f                                                    ∎

  -- Unary Scott induction for fix′.

  fix′-induction₁ :
    ∀ {p}
    (P : A ⊥ → Set p)
    (P⊥ : P never)
    (P⨆ : ∀ s → (∀ n → P (s [ n ])) → P (⨆ s))
    (f : A → A ⊥) →
    (∀ x → P x → P (x >>= f)) →
    P (fix′ f)
  fix′-induction₁ P P⊥ P⨆ f =
    fix-induction₁ P P⊥ P⨆ ([_⊥→_⊥].monotone-function (f ∗))

-- N-ary Scott induction.

module _ {a p} n
  (As : Fin n → Set a)
  (P : (∀ i → As i ⊥) → Set p)
  (P⊥ : P (λ _ → never))
  (P⨆ : ∀ ss → (∀ n → P (λ i → ss i [ n ])) → P (⨆ ∘ ss))
  where

  open PAF.N-ary n As (λ i → partiality-algebra (As i)) P P⊥ P⨆ public

  fix′-induction :
    (fs : ∀ i → As i → As i ⊥) →
    (∀ xs → P xs → P (λ i → xs i >>= fs i)) →
    P (fix′ ∘ fs)
  fix′-induction fs =
    fix-induction (λ i → [_⊥→_⊥].monotone-function (fs i ∗))

------------------------------------------------------------------------
-- The fixpoint combinator machinery instantiated with dependent
-- functions to the partiality monad

module _ {a b} (A : Set a) (B : A → Set b) where

  -- Partial function transformers.

  Trans : Set (a ⊔ b)
  Trans = ((x : A) → B x ⊥) → ((x : A) → B x ⊥)

  -- A partiality algebra.

  Pi : Partiality-algebra (a ⊔ b) (a ⊔ b) ((x : A) → B x)
  Pi = Π A (partiality-algebra ∘ B)

  -- Monotone partial function transformers.

  Trans-⊑ : Set (a ⊔ b)
  Trans-⊑ = [ Pi ⟶ Pi ]⊑

  private

    sanity-check : Trans-⊑ → Trans
    sanity-check = [_⟶_]⊑.function

  -- Partial function transformers that are ω-continuous.

  Trans-ω : Set (a ⊔ b)
  Trans-ω = [ Pi ⟶ Pi ]

module _ {a b} {A : Set a} {B : A → Set b} where

  module Trans-⊑ = [_⟶_]⊑ {P₁ = Pi A B} {P₂ = Pi A B}
  module Trans-ω = [_⟶_]  {P₁ = Pi A B} {P₂ = Pi A B}

  private
    module F = PAF.Fix {P = Pi A B}

  -- Applies an increasing sequence of functions to a value.

  at :
    (∃ λ (f : ℕ → (x : A) → B x ⊥) → ∀ n x → f n x ⊑ f (suc n) x) →
    (x : A) → ∃ λ (f : ℕ → B x ⊥) → ∀ n → f n ⊑ f (suc n)
  at = Pi.at (partiality-algebra ∘ B)

  -- Repeated application of a monotone partial function transformer
  -- to the least element.

  app→ : Trans-⊑ A B → ℕ → ((x : A) → B x ⊥)
  app→ = F.app

  -- The increasing sequence fix→-sequence f consists of the elements
  -- const never, Trans-⊑.function f (const never), and so on. This
  -- sequence is used in the implementation of fix→.

  fix→-sequence : Trans-⊑ A B →
                  Partiality-algebra.Increasing-sequence (Pi A B)
  fix→-sequence = F.fix-sequence

  -- A fixpoint combinator.

  fix→ : Trans-⊑ A B → ((x : A) → B x ⊥)
  fix→ = F.fix

  -- The fixpoint combinator produces fixpoints for ω-continuous
  -- arguments.

  fix→-is-fixpoint-combinator :
    (f : Trans-ω A B) →
    fix→ (Trans-ω.monotone-function f) ≡
    Trans-ω.function f (fix→ (Trans-ω.monotone-function f))
  fix→-is-fixpoint-combinator = F.fix-is-fixpoint-combinator

  -- The result of the fixpoint combinator is pointwise smaller than
  -- or equal to every "pointwise post-fixpoint".

  fix→-is-least :
    (f : Trans-⊑ A B) →
    ∀ g → (∀ x → Trans-⊑.function f g x ⊑ g x) →
      ∀ x → fix→ f x ⊑ g x
  fix→-is-least = F.fix-is-least

  -- Taking steps that are "twice as large" does not affect the end
  -- result.

  fix→-∘ : (f : Trans-⊑ A B) → fix→ (f ∘⊑ f) ≡ fix→ f
  fix→-∘ = F.fix-∘

-- N-ary Scott induction.

module _
  {a b p} n
  (As : Fin n → Set a)
  (Bs : (i : Fin n) → As i → Set b)
  (P : (∀ i → (x : As i) → Bs i x ⊥) → Set p)
  (P⊥ : P (λ _ _ → never))
  (P⨆ : (ss : ∀ i (x : As i) → Increasing-sequence (Bs i x)) →
        (∀ n → P (λ i xs → ss i xs [ n ])) →
        P (λ i xs → ⨆ (ss i xs)))
  (fs : ∀ i → Trans-⊑ (As i) (Bs i)) where

  private
    module N = PAF.N-ary n
                 (λ i → (x : As i) → Bs i x)
                 (λ i → Π (As i) (partiality-algebra ∘ Bs i))
                 P
                 P⊥
                 (λ _ → P⨆ _)
                 fs

  -- Generalised.

  fix→-induction′ :
    (∀ n → P (λ i → app→ (fs i) n) →
           P (λ i → app→ (fs i) (suc n))) →
    P (λ i → fix→ (fs i))
  fix→-induction′ = N.fix-induction′

  -- Basic.

  fix→-induction :
    ((gs : ∀ i (x : As i) → Bs i x ⊥) →
     P gs → P (λ i → Trans-⊑.function (fs i) (gs i))) →
    P (λ i → fix→ (fs i))
  fix→-induction = N.fix-induction

-- Unary Scott induction.

fix→-induction₁ :
  ∀ {a b p} {A : Set a} {B : A → Set b}
  (P : ((x : A) → B x ⊥) → Set p) →
  P (λ _ → never) →
  ((s : (x : A) → Increasing-sequence (B x)) →
   (∀ n → P (λ x → s x [ n ])) →
   P (λ x → ⨆ (s x))) →
  (f : Trans-⊑ A B) →
  (∀ g → P g → P (Trans-⊑.function f g)) →
  P (fix→ f)
fix→-induction₁ P P⊥ P⨆ = PAF.fix-induction₁ P P⊥ (λ _ → P⨆ _)

------------------------------------------------------------------------
-- Some combinators that can be used to construct ω-continuous partial
-- function transformers, for use with fix→

-- A type used by these combinators.

record Partial
         {a b c}
         (A : Set a) (B : A → Set b) (C : Set c) :
         Set (a ⊔ b ⊔ lsuc c) where
  field
    -- A function that is allowed to make "recursive calls" of type
    -- (x : A) → B x ⊥.

    function : ((x : A) → B x ⊥) → C ⊥

    -- The function must be monotone.

    monotone : ∀ {rec₁ rec₂} →
               (∀ x → rec₁ x ⊑ rec₂ x) →
               function rec₁ ⊑ function rec₂

  -- The function can be turned into an increasing sequence.

  sequence : ((x : A) → Increasing-sequence (B x)) →
             Increasing-sequence C
  sequence recs =
      (λ n → function (λ x → recs x [ n ]))
    , (λ n → monotone (λ x → increasing (recs x) n))

  field
    -- The function must be ω-continuous in the following sense.
    --
    -- The proof can make use of propositional extensionality. This
    -- assumption is included so that the monad instance can be
    -- defined without a corresponding assumption.

    ω-continuous : Propositional-extensionality c →
                   (recs : (x : A) → Increasing-sequence (B x)) →
                   function (⨆ ∘ recs) ≡ ⨆ (sequence recs)

-- The first two arguments of Partial specify the domain and codomain
-- of "recursive calls".

rec : ∀ {a b} {A : Set a} {B : A → Set b} →
      (x : A) → Partial A B (B x)
rec x = record
  { function     = _$ x
  ; monotone     = _$ x
  ; ω-continuous = λ _ _ → refl
  }

-- Turns certain Partial-valued functions into monotone partial
-- function transformers.

transformer : ∀ {a b} {A : Set a} {B : A → Set b} →
              ((x : A) → Partial A B (B x)) → Trans-⊑ A B
transformer f = record
  { function = λ g     x → function (f x) g
  ; monotone = λ g₁⊑g₂ x → monotone (f x) g₁⊑g₂
  }
  where
  open Partial

-- Turns certain Partial-valued functions into ω-continuous partial
-- function transformers (assuming propositional extensionality).

transformer-ω : ∀ {a b} {A : Set a} {B : A → Set b} →
                Propositional-extensionality b →
                ((x : A) → Partial A B (B x)) → Trans-ω A B
transformer-ω prop-ext f = record
  { monotone-function = transformer f
  ; ω-continuous      = λ _ → ext λ x → ω-continuous (f x) prop-ext _
  }
  where
  open Partial

-- A fixpoint combinator.

fixP : ∀ {a b} {A : Set a} {B : A → Set b} →
       ((x : A) → Partial A B (B x)) → ((x : A) → B x ⊥)
fixP {A = A} {B} =
  ((x : A) → Partial A B (B x))  ↝⟨ transformer ⟩
  Trans-⊑ A B                    ↝⟨ fix→ ⟩□
  ((x : A) → B x ⊥)              □

-- The fixpoint combinator produces fixpoints (assuming propositional
-- extensionality).

fixP-is-fixpoint-combinator :
  ∀ {a b} {A : Set a} {B : A → Set b} →
  Propositional-extensionality b →
  (f : (x : A) → Partial A B (B x)) →
  fixP f ≡ flip (Partial.function ∘ f) (fixP f)
fixP-is-fixpoint-combinator prop-ext =
  fix→-is-fixpoint-combinator ∘ transformer-ω prop-ext

-- The result of the fixpoint combinator is pointwise smaller than
-- or equal to every "pointwise post-fixpoint".

fixP-is-least :
  ∀ {a b} {A : Set a} {B : A → Set b}
  (f : (x : A) → Partial A B (B x)) →
  ∀ g → (∀ x → Partial.function (f x) g ⊑ g x) →
    ∀ x → fixP f x ⊑ g x
fixP-is-least = fix→-is-least ∘ transformer

-- Composition of certain Partial-valued functions.

infixr 40 _∘P_

_∘P_ :
  ∀ {a b} {A : Set a} {B : A → Set b} →
  ((x : A) → Partial A B (B x)) →
  ((x : A) → Partial A B (B x)) →
  ((x : A) → Partial A B (B x))
Partial.function     ((f ∘P g) x) = λ h →
                                      Partial.function (f x) λ y →
                                      Partial.function (g y) h
Partial.monotone     ((f ∘P g) x) = λ hyp →
                                      Partial.monotone (f x) λ y →
                                      Partial.monotone (g y) hyp
Partial.ω-continuous ((f ∘P g) x) = λ prop-ext recs →
  function (f x) (λ y → function (g y) (⨆ ∘ recs))  ≡⟨ cong (function (f x)) (ext λ y → ω-continuous (g y) prop-ext recs) ⟩
  function (f x) (λ y → ⨆ (sequence (g y) recs))    ≡⟨ ω-continuous (f x) prop-ext (λ y → sequence (g y) recs) ⟩∎
  ⨆ (sequence (f x) λ y → sequence (g y) recs)      ∎
  where
  open Partial

-- Taking steps that are "twice as large" does not affect the end
-- result.

fixP-∘ : ∀ {a b} {A : Set a} {B : A → Set b}
         (f : (x : A) → Partial A B (B x)) →
         fixP (f ∘P f) ≡ fixP f
fixP-∘ f =
  fix→ (transformer (f ∘P f))            ≡⟨⟩
  fix→ (transformer f ∘⊑ transformer f)  ≡⟨ fix→-∘ (transformer f) ⟩∎
  fix→ (transformer f)                   ∎

-- N-ary Scott induction.

module _
  {a b p} n
  (As : Fin n → Set a)
  (Bs : (i : Fin n) → As i → Set b)
  (P : (∀ i (x : As i) → Bs i x ⊥) → Set p)
  (P⊥ : P (λ _ _ → never))
  (P⨆ : (ss : ∀ i (x : As i) → Increasing-sequence (Bs i x)) →
        (∀ n → P (λ i xs → ss i xs [ n ])) →
        P (λ i xs → ⨆ (ss i xs)))
  (fs : ∀ i (x : As i) → Partial (As i) (Bs i) (Bs i x)) where

  -- Generalised.

  fixP-induction′ :
    (∀ n → P (λ i → app→ (transformer (fs i)) n) →
           P (λ i → app→ (transformer (fs i)) (suc n))) →
    P (λ i → fixP (fs i))
  fixP-induction′ =
    fix→-induction′ n As Bs P P⊥ P⨆ (transformer ∘ fs)

  -- Basic.

  fixP-induction :
    ((gs : ∀ i (x : As i) → Bs i x ⊥) →
     P gs → P (λ i xs → Partial.function (fs i xs) (gs i))) →
    P (λ i → fixP (fs i))
  fixP-induction =
    fix→-induction n As Bs P P⊥ P⨆ (transformer ∘ fs)

-- Unary Scott induction.

fixP-induction₁ :
  ∀ {a b p} {A : Set a} {B : A → Set b}
  (P : ((x : A) → B x ⊥) → Set p) →
  P (λ _ → never) →
  ((s : (x : A) → Increasing-sequence (B x)) →
   (∀ n → P (λ x → s x [ n ])) →
   P (λ x → ⨆ (s x))) →
  (f : (x : A) → Partial A B (B x)) →
  (∀ g → P g → P (λ x → Partial.function (f x) g)) →
  P (fixP f)
fixP-induction₁ P P⊥ P⨆ f =
  fix→-induction₁ P P⊥ P⨆ (transformer f)

-- Equality characterisation lemma for Partial.

equality-characterisation-Partial :
  ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
    {f g : Partial A B C} →
  (∀ rec → Partial.function f rec ≡ Partial.function g rec) ↔
  f ≡ g
equality-characterisation-Partial {f = f} {g} =
  (∀ rec → function f rec ≡ function g rec)  ↔⟨ Eq.extensionality-isomorphism ext ⟩
  function f ≡ function g                    ↝⟨ ignore-propositional-component
                                                  (Σ-closure 1
                                                     (implicit-Π-closure ext 1 λ _ →
                                                      implicit-Π-closure ext 1 λ _ →
                                                      Π-closure          ext 1 λ _ →
                                                      ⊑-propositional) λ _ →
                                                     Π-closure ext 1 λ _ →
                                                     Π-closure ext 1 λ _ →
                                                     ⊥-is-set _ _) ⟩
  (function f , _) ≡ (function g , _)        ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ lemma) ⟩□
  f ≡ g                                      □
  where
  open Partial

  lemma : Partial _ _ _
            ↔
          ∃ λ _ → ∃ λ (_ : ∀ {rec₁ rec₂} → _ → _) → _
  lemma = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ x → function x , monotone x , ω-continuous x
        ; from = λ { (f , m , ω) → record
                      { function     = f
                      ; monotone     = λ {rec₁ rec₂} → m {rec₁ = rec₁} {rec₂ = rec₂}
                      ; ω-continuous = ω
                      } }
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ _ → refl
    }

-- "Non-recursive" computations can be converted into possibly
-- recursive ones.

non-recursive :
  ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c} →
  C ⊥ → Partial A B C
non-recursive x = record
  { function     = const x
  ; monotone     = const (x ■)
  ; ω-continuous = λ _ _ →
      x             ≡⟨ sym ⨆-const ⟩∎
      ⨆ (constˢ x)  ∎
  }

instance

  -- Partial A B is a monad.

  partial-raw-monad : ∀ {a b c} {A : Set a} {B : A → Set b} →
                      Raw-monad (Partial {c = c} A B)
  Raw-monad.return partial-raw-monad x   = non-recursive (return x)
  Raw-monad._>>=_  partial-raw-monad x f = record
    { function     = λ rec →
                       function x rec >>=′ λ y →
                       function (f y) rec
    ; monotone     = λ rec⊑rec →
                       monotone x rec⊑rec >>=-mono λ y →
                       monotone (f y) rec⊑rec
    ; ω-continuous = λ prop-ext recs →
        (function x (⨆ ∘ recs) >>=′ λ y → function (f y) (⨆ ∘ recs))     ≡⟨ cong₂ _>>=′_ (ω-continuous x prop-ext recs)
                                                                                         (ext λ y → ω-continuous (f y) prop-ext recs) ⟩
        (⨆ (sequence x recs) >>=′ λ y → ⨆ (sequence (f y) recs))         ≡⟨ ⨆->>= ⟩

        ⨆ ( (λ n →
               function x (λ z → recs z [ n ]) >>=′ λ y →
               ⨆ (sequence (f y) recs))
          , _
          )                                                              ≡⟨ ⨆>>=⨆≡⨆>>= prop-ext prop-ext
                                                                                       (sequence x recs)
                                                                                       (λ y → sequence (f y) recs) ⟩∎
        ⨆ ( (λ n → function x (λ z → recs z [ n ]) >>=′ λ y →
                   function (f y) (λ z → recs z [ n ]))
          , _
          )                                                              ∎
    }
    where
    open Partial

  partial-monad : ∀ {a b c} {A : Set a} {B : A → Set b} →
                  Monad (Partial {c = c} A B)
  Monad.raw-monad partial-monad = partial-raw-monad

  Monad.left-identity partial-monad _ f =
    _↔_.to equality-characterisation-Partial
      (λ h → left-identity _ (λ y → Partial.function (f y) h))

  Monad.right-identity partial-monad _ =
    _↔_.to equality-characterisation-Partial
      (λ _ → right-identity _)

  Monad.associativity partial-monad x _ _ =
    _↔_.to equality-characterisation-Partial
      (λ h → associativity (Partial.function x h) _ _)

------------------------------------------------------------------------
-- An example

private

  infixr 5 _∷_

  record Stream {a} (A : Set a) : Set a where
    coinductive
    constructor _∷_
    field
      head : A
      tail : Stream A

  open Stream

  -- A direct implementation of a function that searches a stream for
  -- an element satisfying a predicate.

  module Direct {a} {A : Set a} (q : A → Bool) where

    Φ : Trans (Stream A) (λ _ → A)
    Φ f xs = if q (head xs) then return (head xs) else f (tail xs)

    Φ-monotone :
      ∀ {f₁ f₂} → (∀ xs → f₁ xs ⊑ f₂ xs) → ∀ xs → Φ f₁ xs ⊑ Φ f₂ xs
    Φ-monotone f₁⊑f₂ xs with q (head xs)
    ... | true  = return (head xs)  ■
    ... | false = f₁⊑f₂ (tail xs)

    Φ-⊑ : Trans-⊑ (Stream A) (λ _ → A)
    Φ-⊑ = record { function = Φ; monotone = Φ-monotone }

    search : Stream A → A ⊥
    search = fix→ Φ-⊑

    search-least :
      ∀ f → (∀ xs → Φ f xs ⊑ f xs) →
      ∀ xs → search xs ⊑ f xs
    search-least = fix→-is-least Φ-⊑

    Φ-ω-continuous :
      (s : ∃ λ (f : ℕ → Stream A → A ⊥) →
             ∀ n xs → f n xs ⊑ f (suc n) xs) →
      Φ (⨆ ∘ at s) ≡ ⨆ ∘ at [ Φ-⊑ $ s ]-inc
    Φ-ω-continuous s = ext helper
      where
      helper : ∀ xs → Φ (⨆ ∘ at s) xs ≡ ⨆ (at [ Φ-⊑ $ s ]-inc xs)
      helper xs with q (head xs)
      ... | true  = return (head xs)               ≡⟨ sym ⨆-const ⟩∎
                    ⨆ (constˢ (return (head xs)))  ∎
      ... | false = ⨆ (at s (tail xs))             ∎

    Φ-ω : Trans-ω (Stream A) (λ _ → A)
    Φ-ω = record
      { monotone-function = Φ-⊑
      ; ω-continuous      = Φ-ω-continuous
      }

    search-fixpoint : search ≡ Φ search
    search-fixpoint = fix→-is-fixpoint-combinator Φ-ω

  -- An arguably more convenient implementation, with the potential
  -- drawback that one of the lemmas depends on propositional
  -- extensionality.

  module Indirect {a} {A : Set a} (q : A → Bool) where

    ΦP : Stream A → Partial (Stream A) (λ _ → A) A
    ΦP xs =
      if q (head xs) then
        return (head xs)
      else
        rec (tail xs)

    Φ : Trans (Stream A) (λ _ → A)
    Φ = Trans-⊑.function (transformer ΦP)

    search : Stream A → A ⊥
    search = fixP ΦP

    search-least :
      ∀ f → (∀ xs → Φ f xs ⊑ f xs) →
      ∀ xs → search xs ⊑ f xs
    search-least = fixP-is-least ΦP

    search-fixpoint :
      Propositional-extensionality a →
      search ≡ Φ search
    search-fixpoint prop-ext = fixP-is-fixpoint-combinator prop-ext ΦP
