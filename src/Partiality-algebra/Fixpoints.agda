------------------------------------------------------------------------
-- Fixpoint combinators
------------------------------------------------------------------------

{-# OPTIONS --cubical #-}

open import Partiality-algebra as PA hiding (id; _∘_)

module Partiality-algebra.Fixpoints where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms equality-with-J using (ext)
import Equivalence equality-with-J as Eq
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J hiding (Type)
open import H-level.Closure equality-with-J
open import Monad equality-with-J
open import Univalence-axiom equality-with-J

open import Partiality-algebra.Monotone
open import Partiality-algebra.Omega-continuous
import Partiality-algebra.Properties as PAP

open [_⟶_]⊑

-- The development below, up to fix-is-least, is (very similar to)
-- Kleene's fixed-point theorem.

private
 module Fix₀ {a p q} {A : Set a} {P : Partiality-algebra p q A} where

  open Partiality-algebra P
  open PAP P

  -- Repeated composition of a monotone function with itself.

  comp : [ P ⟶ P ]⊑ → ℕ → [ P ⟶ P ]⊑
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

  -- Repeated application of a monotone function to never.

  app : [ P ⟶ P ]⊑ → ℕ → Type
  app f n = function (comp f n) never

  -- An increasing sequence consisting of repeated applications of the
  -- given monotone function to never.

  fix-sequence : [ P ⟶ P ]⊑ → Increasing-sequence
  fix-sequence f = app f , fix-sequence-increasing
    where
    abstract
      fix-sequence-increasing :
        ∀ n → function (comp f n) never ⊑ function (f ∘⊑ comp f n) never
      fix-sequence-increasing n =
        function (comp f n) never               ⊑⟨ monotone (comp f n) (never⊑ (function f never)) ⟩
        function (comp f n) (function f never)  ⊑⟨⟩
        function (comp f n ∘⊑ f) never          ≡⟨ cong (λ g → function g never) $ pre≡post f n ⟩⊑
        function (f ∘⊑ comp f n) never          ■

  -- Taking the tail of this sequence amounts to the same thing as
  -- applying the function to each element in the sequence.

  tailˢ-fix-sequence :
    (f : [ P ⟶ P ]⊑) →
    tailˢ (fix-sequence f) ≡ [ f $ fix-sequence f ]-inc
  tailˢ-fix-sequence f =
    _↔_.to equality-characterisation-increasing λ _ → refl

  -- The sequence has the same least upper bound as the sequence you get
  -- if you apply the function to each element of the sequence.

  ⨆-fix-sequence :
    (f : [ P ⟶ P ]⊑) →
    ⨆ (fix-sequence f) ≡ ⨆ [ f $ fix-sequence f ]-inc
  ⨆-fix-sequence f =
    ⨆ (fix-sequence f)            ≡⟨ sym $ ⨆tail≡⨆ _ ⟩
    ⨆ (tailˢ (fix-sequence f))    ≡⟨ cong ⨆ (tailˢ-fix-sequence f) ⟩∎
    ⨆ [ f $ fix-sequence f ]-inc  ∎

  -- A fixpoint combinator.

  fix : [ P ⟶ P ]⊑ → Type
  fix f = ⨆ (fix-sequence f)

  -- The fixpoint combinator produces fixpoints for ω-continuous
  -- arguments.

  fix-is-fixpoint-combinator :
    (fω : [ P ⟶ P ]) →
    let f : [ P ⟶ P ]⊑
        f = [_⟶_].monotone-function fω
    in fix f ≡ function f (fix f)
  fix-is-fixpoint-combinator fω =
    fix f                            ≡⟨⟩
    ⨆ (fix-sequence f)               ≡⟨ ⨆-fix-sequence f ⟩
    ⨆ [ f $ fix-sequence f ]-inc     ≡⟨ sym $ [_⟶_].ω-continuous fω _ ⟩
    function f (⨆ (fix-sequence f))  ≡⟨⟩
    function f (fix f)               ∎
    where
    f : [ P ⟶ P ]⊑
    f = [_⟶_].monotone-function fω

  -- The result of the fixpoint combinator is smaller than or equal to
  -- every post-fixpoint.

  fix-is-least :
    (f : [ P ⟶ P ]⊑) →
    ∀ x → function f x ⊑ x → fix f ⊑ x
  fix-is-least f x fx⊑x = least-upper-bound _ _ lemma
    where
    lemma : ∀ n → function (comp f n) never ⊑ x
    lemma zero    = never⊑ x
    lemma (suc n) =
      function (f ∘⊑ comp f n) never          ⊑⟨⟩
      function f (function (comp f n) never)  ⊑⟨ monotone f (lemma n) ⟩
      function f x                            ⊑⟨ fx⊑x ⟩■
      x                                       ■

  -- A restricted homomorphism property.

  comp-∘ : ∀ f n → comp (f ∘⊑ f) n ≡ comp f n ∘⊑ comp f n
  comp-∘ f zero    = id⊑  ∎
  comp-∘ f (suc n) =
    (f ∘⊑ f) ∘⊑ comp (f ∘⊑ f) n         ≡⟨ cong ((f ∘⊑ f) ∘⊑_) (comp-∘ f n) ⟩
    (f ∘⊑ f) ∘⊑ (comp f n ∘⊑ comp f n)  ≡⟨ lemma f f (comp f n) _ ⟩
    f ∘⊑ ((f ∘⊑ comp f n) ∘⊑ comp f n)  ≡⟨ cong ((_∘⊑ comp f n) ∘ (f ∘⊑_)) $ sym $ pre≡post f n ⟩
    f ∘⊑ ((comp f n ∘⊑ f) ∘⊑ comp f n)  ≡⟨ sym $ lemma f (comp f n) f _ ⟩∎
    (f ∘⊑ comp f n) ∘⊑ (f ∘⊑ comp f n)  ∎
    where
    lemma : (f g h k : [ P ⟶ P ]⊑) →
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

  fix-∘ : (f : [ P ⟶ P ]⊑) → fix (f ∘⊑ f) ≡ fix f
  fix-∘ f = antisymmetry
    (least-upper-bound _ _ λ n →
       function (comp (f ∘⊑ f) n) never       ≡⟨ cong (λ f → function f never) $ comp-∘ f n ⟩⊑
       function (comp f n ∘⊑ comp f n) never  ≡⟨ cong (λ f → function f never) $ sym $ comp-+∘ f n ⟩⊑
       function (comp f (n + n)) never        ⊑⟨ upper-bound (fix-sequence f) (n + n) ⟩■
       ⨆ (fix-sequence f)                     ■)
    (⨆-mono λ n →
       function (comp f n) never                        ⊑⟨ monotone (comp f n) (never⊑ _) ⟩
       function (comp f n) (function (comp f n) never)  ⊑⟨⟩
       function (comp f n ∘⊑ comp f n) never            ≡⟨ cong (λ f → function f never) $ sym $ comp-∘ f n ⟩⊑
       function (comp (f ∘⊑ f) n) never                 ■)

open Fix₀

-- N-ary Scott induction.

module N-ary
  (open Partiality-algebra)
  {a p q r} n
  (As : Fin n → Set a)
  (Ps : ∀ i → Partiality-algebra p q (As i))
  (P : (∀ i → Type (Ps i)) → Set r)
  (P⊥ : P (λ i → never (Ps i)))
  (P⨆ : (ss : ∀ i → Increasing-sequence (Ps i)) →
        (∀ n → P (λ i → _[_] (Ps i) (ss i) n)) →
        P (λ i → ⨆ (Ps i) (ss i)))
  (fs : ∀ i → [ Ps i ⟶ Ps i ]⊑)
  where

  -- Generalised.

  fix-induction′ :
    (∀ n → P (λ i → app (fs i) n) → P (λ i → app (fs i) (suc n))) →
    P (fix ∘ fs)
  fix-induction′ step =                       $⟨ lemma ⟩
    (∀ n → P (λ i → app (fs i) n))            ↝⟨ P⨆ _ ⟩
    P (λ i → ⨆ (Ps i) (fix-sequence (fs i)))  ↝⟨ id ⟩□
    P (fix ∘ fs)                              □
    where
    lemma : ∀ n → P (λ i → function (comp (fs i) n) (never (Ps i)))
    lemma zero    = P⊥
    lemma (suc n) =                             $⟨ lemma n ⟩
      P (λ i → app (fs i) n)                    ↝⟨ step n ⟩□
      P (λ i → function (fs i) (app (fs i) n))  □

  -- Basic.

  fix-induction :
    (∀ xs → P xs → P (λ i → function (fs i) (xs i))) →
    P (fix ∘ fs)
  fix-induction step =
    fix-induction′ (λ n → step (λ i → app (fs i) n))

open N-ary public

module Fix {a p q} {A : Set a} {P : Partiality-algebra p q A} where

  open Partiality-algebra P

  -- Unary Scott induction.

  fix-induction₁ :
    ∀ {r}
    (Q : Type → Set r) →
    Q never →
    (∀ s → (∀ n → Q (s [ n ])) → Q (⨆ s)) →
    (f : [ P ⟶ P ]⊑) →
    (∀ x → Q x → Q (function f x)) →
    Q (fix f)
  fix-induction₁ Q Q⊥ Q⨆ f step =
    fix-induction
      1
      [ const A ,        ⊥-elim    ]
      [ const P , (λ i → ⊥-elim i) ]
      (Q ∘ (_$ fzero))
      Q⊥
      (Q⨆ ∘ (_$ fzero))
      [ const f , (λ x → ⊥-elim x) ]
      (step ∘ (_$ fzero))

  open Fix₀ {P = P} public

open Fix public
