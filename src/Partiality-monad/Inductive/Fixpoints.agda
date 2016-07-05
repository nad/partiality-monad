------------------------------------------------------------------------
-- Fixpoint combinators
------------------------------------------------------------------------

{-# OPTIONS --without-K --rewriting #-}

module Partiality-monad.Inductive.Fixpoints where

open import Equality.Propositional
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
import Equivalence equality-with-J as Eq
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Monad equality-with-J
open import Univalence-axiom equality-with-J

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Monad
open import Partiality-monad.Inductive.Monotone
open import Partiality-monad.Inductive.Omega-continuous
open import Partiality-monad.Inductive.Properties

------------------------------------------------------------------------
-- A fixpoint combinator

module _ {a} {A : Set a} where

  -- Repeated composition of a monotone function with itself.

  comp : [ A ⊥→ A ⊥]⊑ → ℕ → [ A ⊥→ A ⊥]⊑
  comp f zero    = id⊑
  comp f (suc n) = comp f n ∘⊑ f

  -- Pre-composition with the function is pointwise equal to
  -- post-composition with the function.

  pre≡post : ∀ f n {x} →
             proj₁ (comp f n ∘⊑ f) x ≡ proj₁ (f ∘⊑ comp f n) x
  pre≡post f zero        = refl
  pre≡post f (suc n) {x} =
    proj₁ (comp f n ∘⊑ f) (proj₁ f x)  ≡⟨ pre≡post f n ⟩∎
    proj₁ (f ∘⊑ comp f n) (proj₁ f x)  ∎

  -- An increasing sequence consisting of repeated applications of the
  -- given monotone function to never.

  fix-sequence : [ A ⊥→ A ⊥]⊑ → Increasing-sequence A
  fix-sequence f =
      (λ n → proj₁ (comp f n) never)
    , (λ n →
         proj₁ (comp f n) never            ⊑⟨ proj₂ (comp f n) (never⊑ (proj₁ f never)) ⟩■
         proj₁ (comp f n) (proj₁ f never)  ■)

  -- Taking the tail of this sequence amounts to the same thing as
  -- applying the function to each element in the sequence.

  tailˢ-fix-sequence :
    (f : [ A ⊥→ A ⊥]⊑) →
    tailˢ (fix-sequence f) ≡ [ f $ fix-sequence f ]-inc
  tailˢ-fix-sequence f =
    _↔_.to equality-characterisation-increasing λ n →
      proj₁ (comp f n ∘⊑ f) never  ≡⟨ pre≡post f n ⟩∎
      proj₁ (f ∘⊑ comp f n) never  ∎

  -- The sequence has the same least upper bound as the sequence you
  -- get if you apply the function to each element of the sequence.

  ⨆-fix-sequence :
    (f : [ A ⊥→ A ⊥]⊑) →
    ⨆ (fix-sequence f) ≡ ⨆ [ f $ fix-sequence f ]-inc
  ⨆-fix-sequence f =
    ⨆ (fix-sequence f)            ≡⟨ sym $ ⨆tail≡⨆ _ ⟩
    ⨆ (tailˢ (fix-sequence f))    ≡⟨ cong ⨆ (tailˢ-fix-sequence f) ⟩∎
    ⨆ [ f $ fix-sequence f ]-inc  ∎

  -- A fixpoint combinator.

  fix : [ A ⊥→ A ⊥]⊑ → A ⊥
  fix f = ⨆ (fix-sequence f)

  -- The fixpoint combinator produces fixpoints for ω-continuous
  -- arguments.

  fix-is-fixpoint-combinator :
    (fω : [ A ⊥→ A ⊥]) →
    let f⊑ : [ A ⊥→ A ⊥]⊑
        f⊑ = proj₁ fω

        f : A ⊥ → A ⊥
        f = proj₁ f⊑
    in fix f⊑ ≡ f (fix f⊑)
  fix-is-fixpoint-combinator fω =
    fix f⊑                          ≡⟨⟩
    ⨆ (fix-sequence f⊑)             ≡⟨ ⨆-fix-sequence f⊑ ⟩
    ⨆ [ f⊑ $ fix-sequence f⊑ ]-inc  ≡⟨ sym $ proj₂ fω _ ⟩
    f (⨆ (fix-sequence f⊑))         ≡⟨ refl ⟩∎
    f (fix f⊑)                      ∎
    where
    f⊑ : [ A ⊥→ A ⊥]⊑
    f⊑ = proj₁ fω

    f : A ⊥ → A ⊥
    f = proj₁ f⊑

  -- A variant of fix.

  fix′ : (A → A ⊥) → A ⊥
  fix′ f = fix (proj₁ (f ∗))

  -- This variant also produces a kind of fixpoint.

  fix′-is-fixpoint-combinator :
    (f : A → A ⊥) →
    fix′ f ≡ fix′ f >>= f
  fix′-is-fixpoint-combinator f =
    fix′ f                   ≡⟨⟩
    fix (proj₁ (f ∗))        ≡⟨ fix-is-fixpoint-combinator (f ∗) ⟩∎
    fix (proj₁ (f ∗)) >>= f  ∎

-- N-ary Scott induction.

module _ {a p} n
  (As : Fin n → Set a)
  (P : (∀ i → As i ⊥) → Set p)
  (P⊥ : P (λ _ → never))
  (P⨆ : ∀ ss → (∀ n → P (λ i → ss i [ n ])) → P (⨆ ∘ ss))
  where

  fix-induction :
    (fs : ∀ i → [ As i ⊥→ As i ⊥]⊑) →
    (∀ xs → P xs → P (λ i → proj₁ (fs i) (xs i))) →
    P (fix ∘ fs)
  fix-induction fs⊑ step =
                                                    $⟨ lemma ⟩
    (∀ n → P (λ i → proj₁ (comp (fs⊑ i) n) never))  ↝⟨ P⨆ _ ⟩
    P (⨆ ∘ fix-sequence ∘ fs⊑)                      ↝⟨ id ⟩□
    P (fix ∘ fs⊑)                                   □
    where
    fs : ∀ i → As i ⊥ → As i ⊥
    fs = proj₁ ∘ fs⊑

    lemma : ∀ n → P (λ i → proj₁ (comp (fs⊑ i) n) never)
    lemma zero    = P⊥
    lemma (suc n) =
                                                     $⟨ lemma n ⟩
      P (λ i → proj₁ (comp (fs⊑ i) n) never)         ↝⟨ step _ ⟩
      P (λ i → fs i (proj₁ (comp (fs⊑ i) n) never))  ↝⟨ ≡⇒↝ implication (cong P $ sym $ ext λ i → pre≡post (fs⊑ i) n) ⟩□
      P (λ i → proj₁ (comp (fs⊑ i) n) (fs i never))  □

  fix′-induction :
    (fs : ∀ i → As i → As i ⊥) →
    (∀ xs → P xs → P (λ i → xs i >>= fs i)) →
    P (fix′ ∘ fs)
  fix′-induction fs = fix-induction (λ i → proj₁ (fs i ∗))

-- Unary Scott induction.

module _ {a p}
  {A : Set a}
  (P : A ⊥ → Set p)
  (P⊥ : P never)
  (P⨆ : ∀ s → (∀ n → P (s [ n ])) → P (⨆ s))
  where

  fix-induction₁ :
    (f : [ A ⊥→ A ⊥]⊑) →
    (∀ x → P x → P (proj₁ f x)) →
    P (fix f)
  fix-induction₁ f step =
    fix-induction
      1
      [ const A , ⊥-elim ]
      (P ∘ (_$ fzero))
      P⊥
      (P⨆ ∘ (_$ fzero))
      [ const f , (λ x → ⊥-elim x) ]
      (step ∘ (_$ fzero))

  fix′-induction₁ :
    (f : A → A ⊥) →
    (∀ x → P x → P (x >>= f)) →
    P (fix′ f)
  fix′-induction₁ f = fix-induction₁ (proj₁ (f ∗))

------------------------------------------------------------------------
-- Another fixpoint combinator

-- TODO: Is it possible to find some suitable abstraction and have
-- only one implementation of a fixpoint combinator?

-- Partial function transformers.

Trans : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Trans A B = (A → B ⊥) → (A → B ⊥)

-- Monotone partial function transformers.

Trans-⊑ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Trans-⊑ A B = ∃ λ (f : (A → B ⊥) → (A → B ⊥)) →
            ∀ {g₁ g₂} → (∀ x → g₁ x ⊑ g₂ x) → ∀ x → f g₁ x ⊑ f g₂ x

-- Monotone partial function transformers can be turned into
-- parametrised increasing sequence transformers.

[_$_at_]-inc :
  ∀ {a b} {A : Set a} {B : Set b} →
  Trans-⊑ A B →
  (A → Increasing-sequence B) → (A → Increasing-sequence B)
[ f $ s at x ]-inc =
    (λ n → proj₁ f (λ x → s x [ n ]) x)
  , (λ n → proj₂ f (λ x → increasing (s x) n) x)

-- Partial function transformers that are ω-continuous.

Trans-ω : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Trans-ω A B = ∃ λ (f : Trans-⊑ A B) →
                (s : A → Increasing-sequence B) (x : A) →
                proj₁ f (⨆ ∘ s) x ≡ ⨆ [ f $ s at x ]-inc

module _ {a b} {A : Set a} {B : Set b} where

  -- Repeated application of a partial function transformer to never.

  app : Trans A B → ℕ → (A → B ⊥)
  app f zero    = const never
  app f (suc n) = f (app f n)

  -- An increasing sequence consisting of repeated applications of the
  -- given partial function transformer to never.

  fix→-sequence : (f : Trans-⊑ A B) → A → Increasing-sequence B
  fix→-sequence f x =
      (λ n → app (proj₁ f) n x)
    , (λ n →
         app (proj₁ f) n       x  ⊑⟨ app-increasing n x ⟩■
         app (proj₁ f) (suc n) x  ■)
    where
    app-increasing :
      ∀ n x → app (proj₁ f) n x ⊑ app (proj₁ f) (suc n) x
    app-increasing zero    = never⊑ ∘ proj₁ f (const never)
    app-increasing (suc n) = proj₂ f (app-increasing n)

  -- A fixpoint combinator.

  fix→ : Trans-⊑ A B → (A → B ⊥)
  fix→ f x = ⨆ (fix→-sequence f x)

  -- The fixpoint combinator produces fixpoints for ω-continuous
  -- arguments.

  fix→-is-fixpoint-combinator :
    (fω : Trans-ω A B) →
    let f⊑ : Trans-⊑ A B
        f⊑ = proj₁ fω

        f : Trans A B
        f = proj₁ f⊑
    in
    fix→ f⊑ ≡ f (fix→ f⊑)
  fix→-is-fixpoint-combinator (f , ω-cont) = ext λ x →
    fix→ f x                            ≡⟨⟩
    ⨆ (fix→-sequence f x)               ≡⟨ sym $ ⨆tail≡⨆ _ ⟩
    ⨆ (tailˢ (fix→-sequence f x))       ≡⟨ cong ⨆ (_↔_.to equality-characterisation-increasing (λ _ → refl)) ⟩
    ⨆ [ f $ fix→-sequence f at x ]-inc  ≡⟨ sym $ ω-cont (fix→-sequence f) x ⟩
    proj₁ f (⨆ ∘ fix→-sequence f) x     ≡⟨ refl ⟩∎
    proj₁ f (fix→ f) x                  ∎

-- N-ary Scott induction.

fix→-induction :
  ∀ {a b p} n
  (As : Fin n → Set a)
  (Bs : Fin n → Set b)
  (P : (∀ i → As i → Bs i ⊥) → Set p) →
  P (λ _ _ → never) →
  ((ss : ∀ i → As i → Increasing-sequence (Bs i)) →
   (∀ n → P (λ i xs → ss i xs [ n ])) →
   P (λ i xs → ⨆ (ss i xs))) →
  (fs : ∀ i → Trans-⊑ (As i) (Bs i)) →
  ((gs : ∀ i → As i → Bs i ⊥) →
   P gs → P (λ i → proj₁ (fs i) (gs i))) →
  P (λ i → fix→ (fs i))
fix→-induction _ As Bs P P⊥ P⨆ fs⊑ step =
                                    $⟨ lemma ⟩
  (∀ n → P (λ i → app (fs i) n))    ↝⟨ P⨆ _ ⟩
  P ((⨆ ∘_) ∘ fix→-sequence ∘ fs⊑)  ↝⟨ id ⟩□
  P (fix→ ∘ fs⊑)                    □
  where
  fs : ∀ i → Trans (As i) (Bs i)
  fs = proj₁ ∘ fs⊑

  lemma : ∀ n → P (λ i → app (fs i) n)
  lemma zero    = P⊥
  lemma (suc n) =
                                         $⟨ lemma n ⟩
    P (λ i xs → app (fs i) n xs)         ↝⟨ step _ ⟩□
    P (λ i xs → fs i (app (fs i) n) xs)  □

-- Unary Scott induction.

fix→-induction₁ :
  ∀ {a b p} {A : Set a} {B : Set b}
  (P : (A → B ⊥) → Set p) →
  P (const never) →
  ((s : A → Increasing-sequence B) →
   (∀ n → P (λ x → s x [ n ])) →
   P (λ x → ⨆ (s x))) →
  (f : Trans-⊑ A B) →
  (∀ g → P g → P (proj₁ f g)) →
  P (fix→ f)
fix→-induction₁ P P⊥ P⨆ f step =
  fix→-induction
    1
    [ const _ , ⊥-elim ]
    [ const _ , ⊥-elim ]
    (P ∘ (_$ fzero))
    P⊥
    (P⨆ ∘ (_$ fzero))
    [ const f , (λ x → ⊥-elim x) ]
    (step ∘ (_$ fzero))

------------------------------------------------------------------------
-- Some combinators that can be used to construct ω-continuous partial
-- function transformers, for use with fix→

-- A type used by these combinators.

record Partial
         {a b c}
         (A : Set a) (B : Set b) (C : Set c) :
         Set (a ⊔ b ⊔ lsuc c) where
  field
    -- A function that is allowed to make "recursive calls" of type
    -- A → B ⊥.

    function : (A → B ⊥) → C ⊥

    -- The function must be monotone.

    monotone : ∀ {rec₁ rec₂} →
               (∀ x → rec₁ x ⊑ rec₂ x) →
               function rec₁ ⊑ function rec₂

  -- The function can be turned into an increasing sequence.

  sequence : (A → Increasing-sequence B) → Increasing-sequence C
  sequence recs =
      (λ n → function (λ x → recs x [ n ]))
    , (λ n → monotone (λ x → increasing (recs x) n))

  field
    -- The function must be ω-continuous in the following sense.
    --
    -- The proof can make use of univalence. This assumption is
    -- included so that the monad instance can be defined without a
    -- univalence assumption.

    ω-continuous : Univalence c →
                   (recs : A → Increasing-sequence B) →
                   function (⨆ ∘ recs) ≡ ⨆ (sequence recs)

open Partial

-- The first two arguments of Partial specify the domain and codomain
-- of "recursive calls".

rec : ∀ {a b} {A : Set a} {B : Set b} → A → Partial A B B
rec x = record
  { function     = _$ x
  ; monotone     = _$ x
  ; ω-continuous = λ _ _ → refl
  }

-- Turns certain Partial-valued functions into monotone partial
-- function transformers.

transformer : ∀ {a b} {A : Set a} {B : Set b} →
              (A → Partial A B B) → Trans-⊑ A B
transformer f =
    (λ g     x → function (f x) g)
  , (λ g₁⊑g₂ x → monotone (f x) g₁⊑g₂)

-- Turns certain Partial-valued functions into ω-continuous partial
-- function transformers (assuming univalence).

transformer-ω : ∀ {a b} {A : Set a} {B : Set b} →
                Univalence b →
                (A → Partial A B B) → Trans-ω A B
transformer-ω univ f =
    transformer f
  , (λ s x → ω-continuous (f x) univ s)

-- A fixpoint combinator.

fixP : ∀ {a b} {A : Set a} {B : Set b} →
       (A → Partial A B B) → (A → B ⊥)
fixP {A = A} {B} =
  (A → Partial A B B)  ↝⟨ transformer ⟩
  Trans-⊑ A B          ↝⟨ fix→ ⟩□
  (A → B ⊥)            □

-- The fixpoint combinator produces fixpoints (assuming univalence).

fixP-is-fixpoint-combinator :
  ∀ {a b} {A : Set a} {B : Set b} →
  Univalence b →
  (f : A → Partial A B B) →
  fixP f ≡ flip (function ∘ f) (fixP f)
fixP-is-fixpoint-combinator univ =
  fix→-is-fixpoint-combinator ∘ transformer-ω univ

-- N-ary Scott induction.

fixP-induction :
  ∀ {a b p} n
  (As : Fin n → Set a)
  (Bs : Fin n → Set b)
  (P : (∀ i → As i → Bs i ⊥) → Set p) →
  P (λ _ _ → never) →
  ((ss : ∀ i → As i → Increasing-sequence (Bs i)) →
   (∀ n → P (λ i xs → ss i xs [ n ])) →
   P (λ i xs → ⨆ (ss i xs))) →
  (fs : ∀ i → As i → Partial (As i) (Bs i) (Bs i)) →
  ((gs : ∀ i → As i → Bs i ⊥) →
   P gs → P (λ i xs → function (fs i xs) (gs i))) →
  P (λ i → fixP (fs i))
fixP-induction n As Bs P P⊥ P⨆ fs =
  fix→-induction n As Bs P P⊥ P⨆ (transformer ∘ fs)

-- Unary Scott induction.

fixP-induction₁ :
  ∀ {a b p} {A : Set a} {B : Set b}
  (P : (A → B ⊥) → Set p) →
  P (const never) →
  ((s : A → Increasing-sequence B) →
   (∀ n → P (λ x → s x [ n ])) →
   P (λ x → ⨆ (s x))) →
  (f : A → Partial A B B) →
  (∀ g → P g → P (λ x → function (f x) g)) →
  P (fixP f)
fixP-induction₁ P P⊥ P⨆ f =
  fix→-induction₁ P P⊥ P⨆ (transformer f)

-- Equality characterisation lemma for Partial.

equality-characterisation-Partial :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
    {f g : Partial A B C} →
  (∀ rec → function f rec ≡ function g rec) ↔
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

instance

  -- Partial A B is a monad.

  partial-monad : ∀ {a b c} {A : Set a} {B : Set b} →
                  Monad (Partial {c = c} A B)
  Raw-monad.return (Monad.raw-monad partial-monad) x = record
    { function     = const (return x)
    ; monotone     = const (return x ■)
    ; ω-continuous = λ _ _ →
        now x               ≡⟨ sym ⨆-const ⟩∎
        ⨆ (constˢ (now x))  ∎
    }

  Raw-monad._>>=_ (Monad.raw-monad partial-monad) x f = record
    { function     = λ rec →
                       function x rec >>=′ λ y →
                       function (f y) rec
    ; monotone     = λ rec⊑rec →
                       monotone x rec⊑rec >>=-mono λ y →
                       monotone (f y) rec⊑rec
    ; ω-continuous = λ univ recs →
        (function x (⨆ ∘ recs) >>=′ λ y → function (f y) (⨆ ∘ recs))     ≡⟨ cong (_>>=′ _) $ ω-continuous x univ recs ⟩

        (⨆ ( (λ n → function x (λ z → recs z [ n ]))
           , (λ n → monotone x (λ z → increasing (recs z) n))
           ) >>=′ λ y → function (f y) (⨆ ∘ recs))                       ≡⟨⟩

        ⨆ ( (λ n → function x (λ z → recs z [ n ]) >>=′ λ y →
                   function (f y) (⨆ ∘ recs))
          , _
          )                                                              ≡⟨ cong ⨆
                                                                              (_↔_.to equality-characterisation-increasing λ n →
                                                                                 cong (function x (λ z → recs z [ n ]) >>=′_) $ ext λ y →
                                                                                   ω-continuous (f y) univ recs) ⟩
        ⨆ ( (λ n →
               function x (λ z → recs z [ n ]) >>=′ λ y →
               ⨆ ( (λ n → function (f y) (λ x → recs x [ n ]))
                 , (λ n → monotone (f y) (λ x → increasing (recs x) n))
                 ))
          , (λ n →
               monotone x (λ z → increasing (recs z) n) >>=-mono λ y →
               ⊑-refl _)
          )                                                              ≡⟨ ⨆>>=⨆≡⨆>>= univ univ
                                                                              ( (λ n → function x (λ z → recs z [ n ]))
                                                                              , (λ n → monotone x (λ z → increasing (recs z) n))
                                                                              ) _ ⟩∎
        ⨆ ( (λ n → function x (λ z → recs z [ n ]) >>=′ λ y →
                   function (f y) (λ z → recs z [ n ]))
          , _
          )                                                              ∎
    }

  Monad.left-identity partial-monad _ f =
    _↔_.to equality-characterisation-Partial
      (λ h → left-identity _ (λ y → function (f y) h))

  Monad.right-identity partial-monad _ =
    _↔_.to equality-characterisation-Partial
      (λ _ → right-identity _)

  Monad.associativity partial-monad x _ _ =
    _↔_.to equality-characterisation-Partial
      (λ h → associativity (function x h) _ _)
