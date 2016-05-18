------------------------------------------------------------------------
-- Some definitions and properties
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Partiality-monad.Inductive.Properties where

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

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Eliminators

module _ {a} {A : Set a} where

  -- _⊑_ is propositional.

  ⊑-propositional : {x y : A ⊥} → Is-proposition (x ⊑ y)
  ⊑-propositional =
    _⇔_.from propositional⇔irrelevant ⊑-proof-irrelevant

  -- ⨆ s is an upper bound for the sequence s.

  upper-bound : (s : Increasing-sequence A) →
                Is-upper-bound s (⨆ s)
  upper-bound s = upper-bound′ s (⨆ s) (⊑-refl (⨆ s))

  -- _⊑_ is transitive.

  ⊑-trans : {x y z : A ⊥} → x ⊑ y → y ⊑ z → x ⊑ z
  ⊑-trans x⊑y = ⊑-rec-⊑ {Q = λ {x y} x⊑y → ∀ {z} → y ⊑ z → x ⊑ z}
    (record
       { qr = λ _ → id
       ; qe = λ _ _ → never⊑ _
       ; qu = λ s ub is-ub n q qu {z} ⨆s⊑z →
                q n (upper-bound′ s z (qu ⨆s⊑z) (suc n))
       ; ql = λ s ub _ _ qu {z} ub⊑z →
                least-upper-bound s z (λ n → qu n ub⊑z)
       ; qp = λ _ → implicit-Π-closure        ext 1 λ _ →
                    Π-closure {a = a} {b = a} ext 1 λ _ →
                    ⊑-propositional
       })
    x⊑y

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

  private

    -- A lemma.

    ⊥-is-set-and-equality-characterisation : Is-set (A ⊥) × _
    ⊥-is-set-and-equality-characterisation =
      Eq.propositional-identity≃≡
        (λ x y → x ⊑ y × x ⊒ y)
        (λ _ _ → ×-closure 1 ⊑-propositional ⊑-propositional)
        (λ x → ⊑-refl x , ⊑-refl x)
        (λ x y → uncurry {B = λ _ → x ⊒ y} antisymmetry)

  -- _⊥ is a family of sets. (This lemma is analogous to
  -- Theorem 11.3.9 in "Homotopy Type Theory: Univalent Foundations of
  -- Mathematics" (first edition).)

  ⊥-is-set : Is-set (A ⊥)
  ⊥-is-set = proj₁ ⊥-is-set-and-equality-characterisation

  -- Equality characterisation lemma for the partiality monad.

  equality-characterisation-⊥ :
    {x y : A ⊥} → (x ⊑ y × x ⊒ y) ≃ (x ≡ y)
  equality-characterisation-⊥ =
    proj₂ ⊥-is-set-and-equality-characterisation ext

  -- Equality characterisation lemma for increasing sequences.

  equality-characterisation-increasing :
    {s₁ s₂ : Increasing-sequence A} →
    (∀ n → s₁ [ n ] ≡ s₂ [ n ]) ↔ s₁ ≡ s₂
  equality-characterisation-increasing {s₁} {s₂} =
    (∀ n → s₁ [ n ] ≡ s₂ [ n ])  ↔⟨ Eq.extensionality-isomorphism ext ⟩
    proj₁ s₁ ≡ proj₁ s₂          ↝⟨ ignore-propositional-component
                                      (Π-closure ext 1 λ _ →
                                       ⊑-propositional) ⟩□
    s₁ ≡ s₂                      □

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

  infix 4 _⇓_

  _⇓_ : A ⊥ → A → Set a
  x ⇓ y = x ≡ now y

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
