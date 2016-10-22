------------------------------------------------------------------------
-- Some definitions and properties
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Partiality-monad.Inductive.Properties {a} {A : Set a} where

open import Equality.Propositional
open import H-level.Truncation.Propositional
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Nat equality-with-J

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Eliminators

-- Preorder reasoning combinators.

infix  -1 finally-⊑
infix  -1 _■
infixr -2 _⊑⟨_⟩_ _⊑⟨⟩_ _⊑⟨_⟩≡_

_⊑⟨_⟩_ : (x {y z} : A ⊥) → x ⊑ y → y ⊑ z → x ⊑ z
_ ⊑⟨ x⊑y ⟩ y⊑z = ⊑-trans x⊑y y⊑z

_⊑⟨⟩_ : (x {y} : A ⊥) → x ⊑ y → x ⊑ y
_ ⊑⟨⟩ x⊑y = x⊑y

_⊑⟨_⟩≡_ : (x {y z} : A ⊥) → x ≡ y →
          y ⊑ z → x ⊑ z
_ ⊑⟨ refl ⟩≡ y⊑z = y⊑z

_■ : (x : A ⊥) → x ⊑ x
x ■ = ⊑-refl x

finally-⊑ : (x y : A ⊥) → x ⊑ y → x ⊑ y
finally-⊑ _ _ x⊑y = x⊑y

syntax finally-⊑ x y x⊑y = x ⊑⟨ x⊑y ⟩■ y ■

-- ⨆ is monotone.

⨆-mono : {s₁ s₂ : Increasing-sequence A} →
         (∀ n → s₁ [ n ] ⊑ s₂ [ n ]) → ⨆ s₁ ⊑ ⨆ s₂
⨆-mono {s₁} {s₂} s₁⊑s₂ =
  least-upper-bound s₁ (⨆ s₂) (λ n →
    s₁ [ n ]  ⊑⟨ s₁⊑s₂ n ⟩
    s₂ [ n ]  ⊑⟨ upper-bound s₂ n ⟩■
    ⨆ s₂      ■)

-- Later elements in an increasing sequence are larger.

later-larger : (s : Increasing-sequence A) →
               ∀ {m n} → m ≤ n → s [ m ] ⊑ s [ n ]
later-larger s {m} (≤-refl′ refl)           = s [ m ] ■
later-larger s {m} (≤-step′ {k = n} p refl) =
  s [ m ]      ⊑⟨ later-larger s p ⟩
  s [ n ]      ⊑⟨ increasing s n ⟩■
  s [ suc n ]  ■

-- The tail of an increasing sequence.

tailˢ : Increasing-sequence A → Increasing-sequence A
tailˢ = Σ-map (_∘ suc) (_∘ suc)

-- The tail has the same least upper bound as the full sequence.

⨆tail≡⨆ : ∀ s → ⨆ (tailˢ s) ≡ ⨆ s
⨆tail≡⨆ s = antisymmetry
  (least-upper-bound (tailˢ s) (⨆ s) (λ n →
     s [ suc n ]  ⊑⟨ upper-bound s (suc n) ⟩■
     ⨆ s          ■))
  (⨆-mono (λ n → s [ n ]      ⊑⟨ increasing s n ⟩■
                 s [ suc n ]  ■))

-- Only never is smaller than or equal to never.

only-never-⊑-never : {x : A ⊥} → x ⊑ never → x ≡ never
only-never-⊑-never x⊑never = antisymmetry x⊑never (never⊑ _)

-- Constant sequences.

constˢ : A ⊥ → Increasing-sequence A
constˢ x = const x , const (⊑-refl x)

-- The least upper bound of a constant sequence is equal to the
-- value in the sequence.

⨆-const : ∀ {x : A ⊥} {inc} → ⨆ (const x , inc) ≡ x
⨆-const {x} =
  antisymmetry (least-upper-bound _ _ (λ _ → ⊑-refl x))
               (upper-bound _ 0)

-- A termination predicate: x ⇓ y means that x terminates with the
-- value y.

infix 4 _⇓_ _⇑

_⇓_ : A ⊥ → A → Set a
x ⇓ y = x ≡ now y

-- A non-termination predicate.

_⇑ : A ⊥ → Set a
x ⇑ = x ≡ never

-- An alternative characterisation of _⊑_.
--
-- For a proof showing that _⊑_ and _≼_ are pointwise equivalent
-- (assuming univalence), see
-- Partiality-monad.Inductive.Alternative-order.≼≃⊑.

_≼_ : A ⊥ → A ⊥ → Set a
x ≼ y = ∀ z → x ⇓ z → y ⇓ z

-- _≼_ is propositional.

≼-propositional : ∀ {x y} → Is-proposition (x ≼ y)
≼-propositional =
  Π-closure ext 1 λ _ →
  Π-closure ext 1 λ _ →
  ⊥-is-set _ _

-- _≼_ is transitive.

≼-trans : ∀ {x y z} → x ≼ y → y ≼ z → x ≼ z
≼-trans {x} {y} {z} x≼y y≼z u =
  x ⇓ u  ↝⟨ x≼y u ⟩
  y ⇓ u  ↝⟨ y≼z u ⟩□
  z ⇓ u  □

-- Box and diamond.

□ : ∀ {ℓ} → (A → Set ℓ) → A ⊥ → Set (a ⊔ ℓ)
□ P x = ∀ y → x ⇓ y → P y

◇ : ∀ {ℓ} → (A → Set ℓ) → A ⊥ → Set (a ⊔ ℓ)
◇ P x = ∥ (∃ λ y → x ⇓ y × P y) ∥

-- All h-levels are closed under box.

□-closure : ∀ {ℓ} {P : A → Set ℓ} {x} n →
            (∀ x → H-level n (P x)) → H-level n (□ P x)
□-closure n h =
  Π-closure ext n λ y →
  Π-closure ext n λ _ →
  h y

-- A "constructor" for ◇. For more "constructors" for □ and ◇, see
-- Partiality-monad.Inductive.Alternative-order.

◇-now :
  ∀ {ℓ} {P : A → Set ℓ} →
  ∀ {x} → P x → ◇ P (now x)
◇-now p = ∣ _ , refl , p ∣

-- Runs the computation. The given number is used to decide which
-- element to choose in sequences that are encountered.

approximate : A ⊥ → ℕ → ∥ Maybe A ∥
approximate x n = ⊥-rec-⊥
  (record
     { pe = ∣ nothing ∣
     ; po = λ x → ∣ just x ∣
     ; pl = λ _ rec → rec n
     ; pp = λ _ → truncation-is-proposition
     })
  x

----------------------------------------------------------------------
-- Combinators that can be used to prove that two least upper bounds
-- are equal

-- For an example of how these combinators can be used, see
-- Lambda.Partiality-monad.Inductive.Compiler-correctness.

-- A relation between sequences.

infix 4 _≳[_]_

record _≳[_]_ (s₁ : ℕ → A ⊥) (n : ℕ) (s₂ : ℕ → A ⊥) : Set a where
  constructor wrap
  field
    run : ∃ λ k → s₁ (k + n) ≡ s₂ n

open _≳[_]_ public

steps-≳ : ∀ {s₁ n s₂} → s₁ ≳[ n ] s₂ → ℕ
steps-≳ = proj₁ ∘ run

-- If two increasing sequences are related in a certain way, then
-- their least upper bounds are equal.

≳→⨆≡⨆ : ∀ {s₁ s₂} k →
        (∀ {n} → proj₁ s₁ ≳[ n ] proj₁ s₂ ∘ (k +_)) →
        ⨆ s₁ ≡ ⨆ s₂
≳→⨆≡⨆ {s₁} {s₂} k s₁≳s₂ = antisymmetry
  (least-upper-bound _ _ λ n →
     let m , s₁[m+n]≡s₂[k+n] = run s₁≳s₂ in

     s₁ [ n ]      ⊑⟨ later-larger s₁ (m≤n+m _ m) ⟩
     s₁ [ m + n ]  ⊑⟨ s₁[m+n]≡s₂[k+n] ⟩≡
     s₂ [ k + n ]  ⊑⟨ upper-bound _ _ ⟩■
     ⨆ s₂          ■)
  (least-upper-bound _ _ λ n →
     let m , s₁[m+n]≡s₂[k+n] = run s₁≳s₂ in

     s₂ [ n ]      ⊑⟨ later-larger s₂ (m≤n+m _ k) ⟩
     s₂ [ k + n ]  ⊑⟨ sym s₁[m+n]≡s₂[k+n] ⟩≡
     s₁ [ m + n ]  ⊑⟨ upper-bound _ _ ⟩■
     ⨆ s₁          ■)

-- Preorder-like reasoning combinators.

infix  -1 _∎≳
infixr -2 _≳⟨⟩_ trans-≳ trans-≡≳ trans-≡≳∀

_∎≳ : ∀ s {n} → s ≳[ n ] s
run (_ ∎≳) = 0 , refl

_≳⟨⟩_ : ∀ {n} s₁ {s₂} → s₁ ≳[ n ] s₂ → s₁ ≳[ n ] s₂
_ ≳⟨⟩ s₁≳s₂ = s₁≳s₂

trans-≳ : ∀ {n} s₁ {s₂ s₃}
          (s₂≳s₃ : s₂ ≳[ n ] s₃) →
          s₁ ≳[ steps-≳ s₂≳s₃ + n ] s₂ →
          s₁ ≳[ n ] s₃
run (trans-≳ {n} s₁ {s₂} {s₃} s₂≳s₃ s₁≳s₂) =
  let k₁ , eq₁ = run s₂≳s₃
      k₂ , eq₂ = run s₁≳s₂
  in
    k₂ + k₁
  , (s₁ ((k₂ + k₁) + n)  ≡⟨ cong s₁ (sym $ +-assoc k₂) ⟩
     s₁ (k₂ + (k₁ + n))  ≡⟨ eq₂ ⟩
     s₂       (k₁ + n)   ≡⟨ eq₁ ⟩∎
     s₃             n    ∎)

trans-≡≳ : ∀ {n} s₁ {s₂ s₃}
           (s₂≳s₃ : s₂ ≳[ n ] s₃) →
           s₁ (steps-≳ s₂≳s₃ + n) ≡ s₂ (steps-≳ s₂≳s₃ + n) →
           s₁ ≳[ n ] s₃
trans-≡≳ _ s₂≳s₃ s₁≡s₂ = _ ≳⟨ wrap (0 , s₁≡s₂) ⟩ s₂≳s₃

trans-≡≳∀ : ∀ {n} s₁ {s₂ s₃} →
            s₂ ≳[ n ] s₃ →
            (∀ n → s₁ n ≡ s₂ n) →
            s₁ ≳[ n ] s₃
trans-≡≳∀ _ s₂≳s₃ s₁≡s₂ = trans-≡≳ _ s₂≳s₃ (s₁≡s₂ _)

syntax trans-≳   s₁ s₂≳s₃ s₁≳s₂ = s₁ ≳⟨ s₁≳s₂ ⟩   s₂≳s₃
syntax trans-≡≳  s₁ s₂≳s₃ s₁≡s₂ = s₁ ≳⟨ s₁≡s₂ ⟩≡  s₂≳s₃
syntax trans-≡≳∀ s₁ s₂≳s₃ s₁≡s₂ = s₁ ≳⟨ s₁≡s₂ ⟩≡∀ s₂≳s₃

-- Some "stepping" combinators.

later : ∀ {n s₁ s₂} →
        s₁ ∘ suc ≳[ n ] s₂ ∘ suc → s₁ ≳[ suc n ] s₂
run (later {n} {s₁} {s₂} s₁≳s₂) =
  let k , eq = run s₁≳s₂
  in
    k
  , (s₁ (k + suc n)  ≡⟨ cong s₁ (sym $ suc+≡+suc k) ⟩
     s₁ (suc k + n)  ≡⟨ eq ⟩∎
     s₂ (suc n)      ∎)

earlier : ∀ {n s₁ s₂} →
          s₁ ≳[ suc n ] s₂ → s₁ ∘ suc ≳[ n ] s₂ ∘ suc
run (earlier {n} {s₁} {s₂} s₁≳s₂) =
  let k , eq = run s₁≳s₂
  in
    k
  , (s₁ (suc k + n)  ≡⟨ cong s₁ (suc+≡+suc k) ⟩
     s₁ (k + suc n)  ≡⟨ eq ⟩∎
     s₂ (suc n)      ∎)

laterˡ : ∀ {n s₁ s₂} → s₁ ∘ suc ≳[ n ] s₂ → s₁ ≳[ n ] s₂
run (laterˡ s₁≳s₂) = Σ-map suc id (run s₁≳s₂)

step⇓ : ∀ {n s} → s ≳[ n ] s ∘ suc
step⇓ = laterˡ (_ ∎≳)
