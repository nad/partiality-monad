------------------------------------------------------------------------
-- Fixpoint combinators
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

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

-- The development below, up to fix-is-least, is (very similar to)
-- Kleene's fixed-point theorem.

module _ {a} {A : Set a} where

  -- Repeated composition of a monotone function with itself.

  comp : [ A ⊥→ A ⊥]⊑ → ℕ → [ A ⊥→ A ⊥]⊑
  comp f zero    = id⊑
  comp f (suc n) = f ∘⊑ comp f n

  -- Pre-composition with the function is equal to post-composition
  -- with the function.

  pre≡post : ∀ f n → comp f n ∘⊑ f ≡ f ∘⊑ comp f n
  pre≡post f zero    = f  ∎
  pre≡post f (suc n) =
    (f ∘⊑ comp f n) ∘⊑ f  ≡⟨ ∘⊑-assoc f (comp f n) ⟩
    f ∘⊑ (comp f n ∘⊑ f)  ≡⟨ cong (f ∘⊑_) $ pre≡post f n ⟩∎
    f ∘⊑ (f ∘⊑ comp f n)  ∎

  -- An increasing sequence consisting of repeated applications of the
  -- given monotone function to never.

  fix-sequence : [ A ⊥→ A ⊥]⊑ → Increasing-sequence A
  fix-sequence f =
      (λ n → proj₁ (comp f n) never)
    , fix-sequence-increasing
    where
    abstract
      fix-sequence-increasing :
        ∀ n → proj₁ (comp f n) never ⊑ proj₁ (f ∘⊑ comp f n) never
      fix-sequence-increasing n =
        proj₁ (comp f n) never            ⊑⟨ proj₂ (comp f n) (never⊑ (proj₁ f never)) ⟩
        proj₁ (comp f n) (proj₁ f never)  ⊑⟨⟩
        proj₁ (comp f n ∘⊑ f) never       ⊑⟨ cong (λ g → proj₁ g never) $ pre≡post f n ⟩≡
        proj₁ (f ∘⊑ comp f n) never       ■

  -- Taking the tail of this sequence amounts to the same thing as
  -- applying the function to each element in the sequence.

  tailˢ-fix-sequence :
    (f : [ A ⊥→ A ⊥]⊑) →
    tailˢ (fix-sequence f) ≡ [ f $ fix-sequence f ]-inc
  tailˢ-fix-sequence f =
    _↔_.to equality-characterisation-increasing λ _ → refl

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

  -- The result of the fixpoint combinator is smaller than or equal to
  -- every post-fixpoint.

  fix-is-least :
    (f : [ A ⊥→ A ⊥]⊑) →
    ∀ x → proj₁ f x ⊑ x → fix f ⊑ x
  fix-is-least f x fx⊑x = least-upper-bound _ _ lemma
    where
    lemma : ∀ n → proj₁ (comp f n) never ⊑ x
    lemma zero    = never⊑ x
    lemma (suc n) =
      proj₁ (f ∘⊑ comp f n) never       ⊑⟨⟩
      proj₁ f (proj₁ (comp f n) never)  ⊑⟨ proj₂ f (lemma n) ⟩
      proj₁ f x                         ⊑⟨ fx⊑x ⟩■
      x                                 ■

  -- The function flip comp n is homomorphic with respect to _∘⊑_.

  comp-∘ : ∀ f n → comp (f ∘⊑ f) n ≡ comp f n ∘⊑ comp f n
  comp-∘ f zero    = id⊑  ∎
  comp-∘ f (suc n) =
    (f ∘⊑ f) ∘⊑ comp (f ∘⊑ f) n         ≡⟨ cong ((f ∘⊑ f) ∘⊑_) (comp-∘ f n) ⟩
    (f ∘⊑ f) ∘⊑ (comp f n ∘⊑ comp f n)  ≡⟨ lemma f f (comp f n) _ ⟩
    f ∘⊑ ((f ∘⊑ comp f n) ∘⊑ comp f n)  ≡⟨ cong ((_∘⊑ comp f n) ∘ (f ∘⊑_)) $ sym $ pre≡post f n ⟩
    f ∘⊑ ((comp f n ∘⊑ f) ∘⊑ comp f n)  ≡⟨ sym $ lemma f (comp f n) f _ ⟩∎
    (f ∘⊑ comp f n) ∘⊑ (f ∘⊑ comp f n)  ∎
    where
    lemma : (f g h k : [ A ⊥→ A ⊥]⊑) →
            (f ∘⊑ g) ∘⊑ (h ∘⊑ k) ≡ f ∘⊑ ((g ∘⊑ h) ∘⊑ k)
    lemma f g h k =
      (f ∘⊑ g) ∘⊑ (h ∘⊑ k)  ≡⟨ ∘⊑-assoc f g ⟩
      f ∘⊑ (g ∘⊑ (h ∘⊑ k))  ≡⟨ cong (f ∘⊑_) $ ∘⊑-assoc g h ⟩∎
      f ∘⊑ ((g ∘⊑ h) ∘⊑ k)  ∎

  -- The function comp f is homomorphic with respect to _+_/_∘⊑_.

  comp-+∘ : ∀ f m {n} → comp f (m + n) ≡ comp f m ∘⊑ comp f n
  comp-+∘ f zero    {n} = comp f n  ∎
  comp-+∘ f (suc m) {n} =
    f ∘⊑ comp f (m + n)          ≡⟨ cong (f ∘⊑_) $ comp-+∘ f m ⟩
    f ∘⊑ (comp f m ∘⊑ comp f n)  ≡⟨ ∘⊑-assoc f (comp f m) ⟩∎
    (f ∘⊑ comp f m) ∘⊑ comp f n  ∎

  -- Taking steps that are "twice as large" does not affect the end
  -- result.

  fix-∘ : (f : [ A ⊥→ A ⊥]⊑) → fix (f ∘⊑ f) ≡ fix f
  fix-∘ f = antisymmetry
    (least-upper-bound _ _ λ n →
       proj₁ (comp (f ∘⊑ f) n) never       ⊑⟨ cong (λ f → proj₁ f never) $ comp-∘ f n ⟩≡
       proj₁ (comp f n ∘⊑ comp f n) never  ⊑⟨ cong (λ f → proj₁ f never) $ sym $ comp-+∘ f n ⟩≡
       proj₁ (comp f (n + n)) never        ⊑⟨ upper-bound (fix-sequence f) (n + n) ⟩■
       ⨆ (fix-sequence f)                  ■)
    (⨆-mono λ n →
       proj₁ (comp f n) never                     ⊑⟨ proj₂ (comp f n) (never⊑ _) ⟩
       proj₁ (comp f n) (proj₁ (comp f n) never)  ⊑⟨⟩
       proj₁ (comp f n ∘⊑ comp f n) never         ⊑⟨ cong (λ f → proj₁ f never) $ sym $ comp-∘ f n ⟩≡
       proj₁ (comp (f ∘⊑ f) n) never              ■)

  -- A variant of fix.

  fix′ : (A → A ⊥) → A ⊥
  fix′ f = fix (proj₁ (f ∗))

  -- This variant also produces a kind of least fixpoint.

  fix′-is-fixpoint-combinator :
    (f : A → A ⊥) →
    fix′ f ≡ fix′ f >>= f
  fix′-is-fixpoint-combinator f =
    fix′ f                   ≡⟨⟩
    fix (proj₁ (f ∗))        ≡⟨ fix-is-fixpoint-combinator (f ∗) ⟩∎
    fix (proj₁ (f ∗)) >>= f  ∎

  fix′-is-least :
    (f : A → A ⊥) →
    ∀ x → x >>= f ⊑ x → fix′ f ⊑ x
  fix′-is-least f = fix-is-least (proj₁ (f ∗))

  -- Taking steps that are "twice as large" does not affect the end
  -- result.

  fix′-∘ : (f : A → A ⊥) → fix′ (λ x → f x >>= f) ≡ fix′ f
  fix′-∘ f =
    fix′ (λ x → f x >>= f)             ≡⟨⟩

    fix (proj₁ ((λ x → f x >>= f) ∗))  ≡⟨ cong fix (_↔_.to equality-characterisation-monotone λ x →

        (x >>= λ y → f y >>= f)             ≡⟨ associativity x f f ⟩∎
        x >>= f >>= f                       ∎) ⟩

    fix (proj₁ (f ∗) ∘⊑ proj₁ (f ∗))   ≡⟨ fix-∘ (proj₁ (f ∗)) ⟩∎

    fix′ f                             ∎

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
      P (λ i → proj₁ (comp (fs⊑ i) n) never)         ↝⟨ step _ ⟩□
      P (λ i → fs i (proj₁ (comp (fs⊑ i) n) never))  □

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

Trans : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Trans A B = ((x : A) → B x ⊥) → ((x : A) → B x ⊥)

-- Monotone partial function transformers.

record Trans-⊑ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  field
    function : Trans A B
    monotone : ∀ {g₁ g₂} →
               (∀ x → g₁ x ⊑ g₂ x) →
               ∀ x → function g₁ x ⊑ function g₂ x

-- Monotone partial function transformers can be turned into
-- parametrised increasing sequence transformers.

[_$_at_]-inc :
  ∀ {a b} {A : Set a} {B : A → Set b} →
  Trans-⊑ A B →
  ((x : A) → Increasing-sequence (B x)) →
  ((x : A) → Increasing-sequence (B x))
[ f $ s at x ]-inc =
    (λ n → function f (λ x → s x [ n ]) x)
  , (λ n → monotone f (λ x → increasing (s x) n) x)
  where
  open Trans-⊑

-- Partial function transformers that are ω-continuous.

record Trans-ω {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  field
    transformer : Trans-⊑ A B

  open Trans-⊑ transformer public

  field
    ω-continuous : (s : (x : A) → Increasing-sequence (B x)) (x : A) →
                   function (⨆ ∘ s) x ≡ ⨆ [ transformer $ s at x ]-inc

module _ {a b} {A : Set a} {B : A → Set b} where

  -- Repeated composition of a partial function transformer with
  -- itself.

  comp→ : Trans A B → ℕ → Trans A B
  comp→ f zero    = id
  comp→ f (suc n) = f ∘ comp→ f n

  -- If the function f is a monotone partial function transformer,
  -- then comp→ f n is monotone.

  comp→-mono :
    ∀ (f : Trans-⊑ A B) n {g h : (x : A) → B x ⊥} →
    (∀ x → g x ⊑ h x) →
    ∀ x → comp→ (Trans-⊑.function f) n g x ⊑
          comp→ (Trans-⊑.function f) n h x
  comp→-mono f zero            g⊑h x = g⊑h x
  comp→-mono f (suc n) {g} {h} g⊑h x =
    function f (comp→ (function f) n g) x  ⊑⟨ monotone f (comp→-mono f n g⊑h) x ⟩
    function f (comp→ (function f) n h) x  ■
    where
    open Trans-⊑

  -- Pre-composition with the partial function transformer is equal to
  -- post-composition.

  pre≡post→ : ∀ f n → comp→ f n ∘ f ≡ f ∘ comp→ f n
  pre≡post→ f zero    = f  ∎
  pre≡post→ f (suc n) =
    f ∘ comp→ f n ∘ f  ≡⟨ cong (f ∘_) (pre≡post→ f n) ⟩
    f ∘ f ∘ comp→ f n  ∎

  -- The function flip comp n is homomorphic with respect to _∘_.

  comp→-∘ : ∀ f n → comp→ (f ∘ f) n ≡ comp→ f n ∘ comp→ f n
  comp→-∘ f zero    = id  ∎
  comp→-∘ f (suc n) =
    f ∘ f ∘ comp→ (f ∘ f) n        ≡⟨ cong ((f ∘ f) ∘_) (comp→-∘ f n) ⟩
    f ∘ f ∘ comp→ f n ∘ comp→ f n  ≡⟨ cong ((_∘ comp→ f n) ∘ (f ∘_)) $ sym $ pre≡post→ f n ⟩
    f ∘ comp→ f n ∘ f ∘ comp→ f n  ∎

  -- The function comp→ f is homomorphic with respect to _+_/_∘_.

  comp→-+∘ : ∀ f m n → comp→ f (m + n) ≡ comp→ f m ∘ comp→ f n
  comp→-+∘ f zero    n = refl
  comp→-+∘ f (suc m) n = cong (f ∘_) (comp→-+∘ f m n)

  -- Repeated application of a partial function transformer to
  -- const never.

  app→ : Trans A B → ℕ → ((x : A) → B x ⊥)
  app→ f n = comp→ f n (λ _ → never)

  -- The increasing sequence fix→-sequence f x consists of the
  -- elements never, function f (const never) x,
  -- function f (function f (const never)) x, and so on.

  fix→-sequence : (f : Trans-⊑ A B) →
                  (x : A) → Increasing-sequence (B x)
  fix→-sequence f x =
      (λ n → app→ (function f) n x)
    , (λ n →
         app→ (function f) n       x  ⊑⟨ app→-increasing n x ⟩■
         app→ (function f) (suc n) x  ■)
    where
    open Trans-⊑

    app→-increasing :
      ∀ n x → app→ (function f) n x ⊑ app→ (function f) (suc n) x
    app→-increasing zero    = never⊑ ∘ function f (λ _ → never)
    app→-increasing (suc n) = monotone f (app→-increasing n)

  -- A fixpoint combinator.

  fix→ : Trans-⊑ A B → ((x : A) → B x ⊥)
  fix→ f x = ⨆ (fix→-sequence f x)

  -- The fixpoint combinator produces fixpoints for ω-continuous
  -- arguments.

  fix→-is-fixpoint-combinator :
    (f : Trans-ω A B) →
    fix→ (Trans-ω.transformer f) ≡
    Trans-ω.function f (fix→ (Trans-ω.transformer f))
  fix→-is-fixpoint-combinator f = ext λ x →
    fix→ (transformer f) x                                        ≡⟨⟩
    ⨆ (fix→-sequence (transformer f) x)                           ≡⟨ sym $ ⨆tail≡⨆ _ ⟩
    ⨆ (tailˢ (fix→-sequence (transformer f) x))                   ≡⟨ cong ⨆ (_↔_.to equality-characterisation-increasing (λ _ → refl)) ⟩
    ⨆ [ transformer f $ fix→-sequence (transformer f) at x ]-inc  ≡⟨ sym $ ω-continuous f (fix→-sequence (transformer f)) x ⟩
    function f (⨆ ∘ fix→-sequence (transformer f)) x              ≡⟨ refl ⟩∎
    function f (fix→ (transformer f)) x                           ∎
    where
    open Trans-ω

  -- The result of the fixpoint combinator is pointwise smaller than
  -- or equal to every "pointwise post-fixpoint".

  fix→-is-least :
    (f : Trans-⊑ A B) →
    ∀ g → (∀ x → Trans-⊑.function f g x ⊑ g x) →
      ∀ x → fix→ f x ⊑ g x
  fix→-is-least f g fg⊑g = least-upper-bound _ _ ∘ lemma
    where
    open Trans-⊑

    lemma : ∀ x n → comp→ (function f) n (λ _ → never) x ⊑ g x
    lemma x zero    = never⊑ (g x)
    lemma x (suc n) =
      function f (comp→ (function f) n (λ _ → never)) x  ⊑⟨ monotone f (λ x → lemma x n) x ⟩
      function f g x                                     ⊑⟨ fg⊑g x ⟩■
      g x                                                ■

  -- Composition of partial function transformers.

  infixr 40 _∘T_

  _∘T_ : Trans-⊑ A B → Trans-⊑ A B → Trans-⊑ A B
  Trans-⊑.function (f ∘T g) = Trans-⊑.function f ∘ Trans-⊑.function g
  Trans-⊑.monotone (f ∘T g) = Trans-⊑.monotone f ∘ Trans-⊑.monotone g

  -- Taking steps that are "twice as large" does not affect the end
  -- result.

  fix→-∘ : (f : Trans-⊑ A B) → fix→ (f ∘T f) ≡ fix→ f
  fix→-∘ f⊑ = ext λ x → antisymmetry
    (least-upper-bound _ _ λ n →
       comp→ (f ∘ f) n (λ _ → never) x          ⊑⟨ cong (λ g → g _ _) $ comp→-∘ f n ⟩≡
       (comp→ f n ∘ comp→ f n) (λ _ → never) x  ⊑⟨ cong (λ f → f (λ _ → never) x) $ sym $ comp→-+∘ f n n ⟩≡
       comp→ f (n + n) (λ _ → never) x          ⊑⟨ upper-bound (fix→-sequence f⊑ x) (n + n) ⟩■
       ⨆ (fix→-sequence f⊑ x)                   ■)
    (⨆-mono λ n →
       comp→ f n (λ _ → never) x                ⊑⟨ comp→-mono f⊑ n (λ _ → never⊑ _) x ⟩
       comp→ f n (comp→ f n (λ _ → never)) x    ⊑⟨⟩
       (comp→ f n ∘ comp→ f n) (λ _ → never) x  ⊑⟨ cong (λ g → g _ _) $ sym $ comp→-∘ f n ⟩≡
       comp→ (f ∘ f) n (λ _ → never) x          ■)
    where
    f = Trans-⊑.function f⊑

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

  -- Generalised.

  fix→-induction′ :
    (∀ n → P (λ i → app→ (Trans-⊑.function (fs i)) n) →
           P (λ i → app→ (Trans-⊑.function (fs i)) (suc n))) →
    P (λ i → fix→ (fs i))
  fix→-induction′ step =              $⟨ lemma ⟩
    (∀ n → P (λ i → app→ (ffs i) n))  ↝⟨ P⨆ _ ⟩
    P ((⨆ ∘_) ∘ fix→-sequence ∘ fs)   ↝⟨ id ⟩□
    P (fix→ ∘ fs)                     □
    where
    open Trans-⊑

    ffs : ∀ i → Trans (As i) (Bs i)
    ffs = function ∘ fs

    lemma : ∀ n → P (λ i → app→ (ffs i) n)
    lemma zero    = P⊥
    lemma (suc n) =                           $⟨ lemma n ⟩
      P (λ i xs → app→ (ffs i) n xs)          ↝⟨ step n ⟩□
      P (λ i xs → ffs i (app→ (ffs i) n) xs)  □

  -- Basic.

  fix→-induction :
    ((gs : ∀ i (x : As i) → Bs i x ⊥) →
     P gs → P (λ i → Trans-⊑.function (fs i) (gs i))) →
    P (λ i → fix→ (fs i))
  fix→-induction step = fix→-induction′ (λ _ → step _)

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
fix→-induction₁ P P⊥ P⨆ f step =
  fix→-induction
    1
    [ const _ , ⊥-elim ]
    [ const _ , (λ x → ⊥-elim x) ]
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
  { transformer  = transformer f
  ; ω-continuous = λ s x → ω-continuous (f x) prop-ext s
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
  fix→ (transformer f ∘T transformer f)  ≡⟨ fix→-∘ (transformer f) ⟩∎
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
    (∀ n → P (λ i → app→ (flip (Partial.function ∘ fs i)) n) →
           P (λ i → app→ (flip (Partial.function ∘ fs i)) (suc n))) →
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
