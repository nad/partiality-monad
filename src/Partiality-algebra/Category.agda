------------------------------------------------------------------------
-- Partiality algebra categories
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Partiality-algebra.Category where

open import Equality.Propositional
open import Interval using (ext; ⟨ext⟩; bad-ext)
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as Bijection using (_↔_)
open import Category equality-with-J as Category
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J hiding (Type)
open import H-level.Closure equality-with-J
open import Structure-identity-principle equality-with-J
open import Univalence-axiom equality-with-J

open import Partiality-algebra as PA hiding (id; _∘_)

------------------------------------------------------------------------
-- Equality characterisation lemmas for Partiality-algebra-with

abstract

  -- An equality characterisation lemma for Partiality-algebra-with.

  equality-characterisation-Partiality-algebra-with₁ :
    ∀ {a p q} {A : Set a} {Type : Set p}
      {P₁ P₂ : Partiality-algebra-with Type q A} →
    let module P₁ = Partiality-algebra-with P₁
        module P₂ = Partiality-algebra-with P₂
    in
    (∃ λ (⊑≡⊑ : ∀ x y → (x P₁.⊑ y) ≡ (x P₂.⊑ y)) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡ P₂.⨆ (Σ-map id (≡⇒→ (⊑≡⊑ _ _) ∘_) s))
      ↔
    P₁ ≡ P₂
  equality-characterisation-Partiality-algebra-with₁
    {q = q} {A} {Type} {P₁} {P₂} =

    (∃ λ (⊑≡⊑ : ∀ x y → (x P₁.⊑ y) ≡ (x P₂.⊑ y)) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡ P₂.⨆ (Σ-map id (≡⇒→ (⊑≡⊑ _ _) ∘_) s))              ↝⟨ ∃-cong (λ ⊑≡⊑ → ∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ s →
                                                                              ≡⇒↝ _ $ cong (λ (p : {f : ℕ → Type} → _) →
                                                                                              P₁.⨆ s ≡ P₂.⨆ (Σ-map id p s)) $
                                                                                _⇔_.to propositional⇔irrelevant
                                                                                  (implicit-Π-closure ext 1 λ _ →
                                                                                   Π-closure          ext 1 λ _ →
                                                                                   Π-closure          ext 1 λ _ →
                                                                                   P₂.⊑-propositional)
                                                                                  (≡⇒→ (⊑≡⊑ _ _) ∘_)
                                                                                  (λ {f} → ≡⇒→ (cong (λ _⊑_ → ∀ n → f n ⊑ f (suc n))
                                                                                                     (⟨ext⟩ (⟨ext⟩ ∘ ⊑≡⊑))))) ⟩
    (∃ λ (⊑≡⊑ : ∀ x y → (x P₁.⊑ y) ≡ (x P₂.⊑ y)) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ (Σ-map id
                         (λ {f} →
                            ≡⇒→ (cong (λ _⊑_ → ∀ n → f n ⊑ f (suc n))
                                      (⟨ext⟩ (⟨ext⟩ ∘ ⊑≡⊑))))
                         s))                                             ↝⟨ Σ-cong (∀-cong ext λ _ →
                                                                                    Eq.extensionality-isomorphism bad-ext) (λ _ → F.id) ⟩
    (∃ λ (⊑≡⊑ : ∀ x → P₁._⊑_ x ≡ P₂._⊑_ x) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ (Σ-map id
                         (λ {f} →
                            ≡⇒→ (cong (λ _⊑_ → ∀ n → f n ⊑ f (suc n))
                                      (⟨ext⟩ ⊑≡⊑)))
                         s))                                             ↝⟨ Σ-cong (Eq.extensionality-isomorphism bad-ext) (λ _ → F.id) ⟩

    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ (Σ-map id
                         (λ {f} →
                            ≡⇒→ (cong (λ _⊑_ → ∀ n → f n ⊑ f (suc n))
                                      ⊑≡⊑))
                         s))                                             ↔⟨⟩

    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ ( proj₁ s
                  , ≡⇒→ (cong (λ _⊑_ →
                                 ∀ n → proj₁ s n ⊑ proj₁ s (suc n))
                              ⊑≡⊑)
                        (proj₂ s)
                  ))                                                     ↝⟨ ∃-cong (λ ⊑≡⊑ → ∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (λ eq → _ ≡ P₂.⨆ (_ , ≡⇒→ eq _)) $ sym $
                                                                                cong-∘ _ _ ⊑≡⊑) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ ( proj₁ s
                  , ≡⇒→ (cong (uncurry λ _⊑_ (f : ℕ → Type) →
                                         ∀ n → f n ⊑ f (suc n))
                              (cong (_, _) ⊑≡⊑))
                        (proj₂ s)
                  ))                                                     ↝⟨ ∃-cong (λ ⊑≡⊑ → ∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (λ inc → _ ≡ P₂.⨆ (_ , inc)) $ sym $
                                                                                subst-in-terms-of-≡⇒↝ equivalence (cong (_, _) ⊑≡⊑) _ _) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ ( proj₁ s
                  , subst (uncurry λ _⊑_ (f : ℕ → Type) →
                                     ∀ n → f n ⊑ f (suc n))
                          (cong (_, _) ⊑≡⊑)
                          (proj₂ s)
                  ))                                                     ↝⟨ ∃-cong (λ ⊑≡⊑ → ∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (λ eq → _ ≡
                                                                                                   P₂.⨆ (_ , subst (uncurry λ _⊑_ (f : ℕ → Type) →
                                                                                                                              ∀ n → f n ⊑ f (suc n))
                                                                                                                   eq _)) $ sym $
                                                                                Σ-≡,≡→≡-subst-const ⊑≡⊑ refl) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ ( proj₁ s
                  , subst (uncurry λ _⊑_ (f : ℕ → Type) →
                                     ∀ n → f n ⊑ f (suc n))
                          (Σ-≡,≡→≡ ⊑≡⊑ (subst-const ⊑≡⊑))
                          (proj₂ s)
                  ))                                                     ↝⟨ ∃-cong (λ ⊑≡⊑ → ∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (λ s → _ ≡ P₂.⨆ s) $ sym $
                                                                                push-subst-pair′ {y≡z = ⊑≡⊑} _ _ (subst-const ⊑≡⊑)) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ (subst (λ _⊑_ → ∃ λ f → ∀ n → f n ⊑ f (suc n))
                         ⊑≡⊑ s))                                         ↝⟨ ∃-cong (λ ⊑≡⊑ → ∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (λ eq → _ ≡
                                                                                                   P₂.⨆ (subst (λ _⊑_ → ∃ λ f → ∀ n →
                                                                                                                          f n ⊑ f (suc n)) eq _)) $
                                                                                sym $ sym-sym ⊑≡⊑) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             P₂.⨆ (subst (λ _⊑_ → ∃ λ f → ∀ n → f n ⊑ f (suc n))
                         (sym (sym ⊑≡⊑)) s))                             ↝⟨ ∃-cong (λ ⊑≡⊑ → ∃-cong λ _ → ∃-cong λ _ → ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (λ f → _ ≡ f _) $ sym $
                                                                                subst-→-domain _ (sym ⊑≡⊑)) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡
             subst (λ _⊑_ → ∃ (λ f → ∀ n → f n ⊑ f (suc n)) → Type)
                   (sym ⊑≡⊑) P₂.⨆ s)                                     ↔⟨ ∃-cong (λ _ → ∃-cong λ _ →
                                                                              Eq.extensionality-isomorphism ext
                                                                                ×-cong
                                                                              Eq.extensionality-isomorphism ext) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       P₁.now ≡ P₂.now
         ×
       P₁.⨆ ≡ subst _ (sym ⊑≡⊑) P₂.⨆)                                    ↝⟨ ∃-cong (λ ⊑≡⊑ → ∃-cong λ _ → ∃-cong λ _ →
                                                                              ≡⇒↝ _ $ elim (λ ⊑≡⊑ → ∀ {⨆₁ ⨆₂} →
                                                                                              (⨆₁ ≡ subst _ (sym ⊑≡⊑) ⨆₂) ≡
                                                                                              (subst _ ⊑≡⊑ ⨆₁ ≡ ⨆₂))
                                                                                           (λ _ → refl) ⊑≡⊑) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       P₁.never ≡ P₂.never
         ×
       P₁.now ≡ P₂.now
         ×
       subst _ ⊑≡⊑ P₁.⨆ ≡ P₂.⨆)                                          ↝⟨ ∃-cong (λ ⊑≡⊑ →
                                                                              ≡⇒↝ _ (cong (_≡ _) $ sym $ subst-const ⊑≡⊑)
                                                                                ×-cong
                                                                              ≡⇒↝ _ (cong (_≡ _) $ sym $ subst-const ⊑≡⊑)
                                                                                ×-cong
                                                                              F.id) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       subst _ ⊑≡⊑ P₁.never ≡ P₂.never
         ×
       subst _ ⊑≡⊑ P₁.now ≡ P₂.now
         ×
       subst _ ⊑≡⊑ P₁.⨆ ≡ P₂.⨆)                                          ↝⟨ ∃-cong (λ _ → ∃-cong λ _ → ≡×≡↔≡) ⟩

    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       subst _ ⊑≡⊑ P₁.never ≡ P₂.never
         ×
       (subst _ ⊑≡⊑ P₁.now , subst _ ⊑≡⊑ P₁.⨆) ≡
       (P₂.now , P₂.⨆))                                                  ↝⟨ ∃-cong (λ _ → ≡×≡↔≡) ⟩

    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       (subst _ ⊑≡⊑ P₁.never , subst _ ⊑≡⊑ P₁.now , subst _ ⊑≡⊑ P₁.⨆) ≡
       (P₂.never , P₂.now , P₂.⨆))                                       ↝⟨ ∃-cong (λ ⊑≡⊑ → ≡⇒↝ _ $ cong (λ x → (subst _ ⊑≡⊑ P₁.never , x) ≡ _) $
                                                                              sym $ push-subst-, {y≡z = ⊑≡⊑} _
                                                                                                 (λ _⊑_ → (∃ λ f → ∀ n → f n ⊑ f (suc n)) → _)) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       (subst _ ⊑≡⊑ P₁.never , subst _ ⊑≡⊑ (P₁.now , P₁.⨆)) ≡
       (P₂.never , P₂.now , P₂.⨆))                                       ↝⟨ ∃-cong (λ ⊑≡⊑ → ≡⇒↝ _ $ cong (_≡ _) $ sym $
                                                                              push-subst-, {y≡z = ⊑≡⊑} _ _) ⟩
    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       subst _ ⊑≡⊑ (P₁.never , P₁.now , P₁.⨆) ≡
       (P₂.never , P₂.now , P₂.⨆))                                       ↔⟨⟩

    (∃ λ (⊑≡⊑ : P₁._⊑_ ≡ P₂._⊑_) →
       subst _ ⊑≡⊑ (proj₂ (proj₁ (_↔_.to rearrange P₁))) ≡
       proj₂ (proj₁ (_↔_.to rearrange P₂)))                              ↝⟨ Bijection.Σ-≡,≡↔≡ ⟩

    proj₁ (_↔_.to rearrange P₁) ≡ proj₁ (_↔_.to rearrange P₂)            ↝⟨ ignore-propositional-component
                                                                              (×-closure 1 (implicit-Π-closure ext 1 λ _ →
                                                                                            implicit-Π-closure ext 1 λ _ →
                                                                                            Π-closure ext 1 λ _ →
                                                                                            Π-closure ext 1 λ _ →
                                                                                            P₂.Type-is-set _ _) $
                                                                               ×-closure 1 (UIP-propositional ext) $
                                                                               ×-closure 1 (Π-closure ext 1 λ _ →
                                                                                            P₂.⊑-propositional) $
                                                                               ×-closure 1 (implicit-Π-closure ext 1 λ _ →
                                                                                            implicit-Π-closure ext 1 λ _ →
                                                                                            implicit-Π-closure ext 1 λ _ →
                                                                                            Π-closure ext 1 λ _ →
                                                                                            Π-closure ext 1 λ _ →
                                                                                            P₂.⊑-propositional) $
                                                                               ×-closure 1 (Π-closure ext 1 λ _ →
                                                                                            P₂.⊑-propositional) $
                                                                               ×-closure 1 (Π-closure ext 1 λ _ →
                                                                                            Π-closure ext 1 λ _ →
                                                                                            P₂.⊑-propositional) $
                                                                               ×-closure 1 (Π-closure ext 1 λ _ →
                                                                                            Π-closure ext 1 λ _ →
                                                                                            Π-closure ext 1 λ _ →
                                                                                            P₂.⊑-propositional)
                                                                                           (implicit-Π-closure ext 1 λ _ →
                                                                                            implicit-Π-closure ext 1 λ _ →
                                                                                            Proof-irrelevant-propositional ext)) ⟩
    _↔_.to rearrange P₁ ≡ _↔_.to rearrange P₂                            ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ rearrange) ⟩□

    P₁ ≡ P₂                                                              □
    where
    module P₁ = Partiality-algebra-with P₁
    module P₂ = Partiality-algebra-with P₂

    rearrange :
      Partiality-algebra-with Type q A
        ↔
      ∃ λ R →
        let _⊑_ : Type → Type → Set q
            _⊑_ = proj₁ R

            never : Type
            never = proj₁ (proj₂ R)

            now : A → Type
            now = proj₁ (proj₂ (proj₂ R))

            ⨆ : (∃ λ (f : ℕ → Type) → ∀ n → f n ⊑ f (suc n)) → Type
            ⨆ = proj₂ (proj₂ (proj₂ R))
        in
        (∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y)
          ×
        Uniqueness-of-identity-proofs Type
          ×
        (∀ x → x ⊑ x)
          ×
        (∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z)
          ×
        (∀ x → never ⊑ x)
          ×
        (∀ s → ∀ n → proj₁ s n ⊑ ⨆ s)
          ×
        (∀ s ub → (∀ n → proj₁ s n ⊑ ub) → ⨆ s ⊑ ub)
          ×
        (∀ {x y} → Proof-irrelevant (x ⊑ y))
    rearrange = record
      { surjection = record
        { logical-equivalence = record
          { to   = λ P → let open Partiality-algebra-with P in
                    ( _⊑_
                    , never
                    , now
                    , ⨆
                    )
                  , antisymmetry
                  , Type-UIP-unused
                  , ⊑-refl
                  , ⊑-trans
                  , never⊑
                  , upper-bound
                  , least-upper-bound
                  , ⊑-proof-irrelevant
          ; from = λ where
              ((LE , ne , n , l) , a , u , r , t , le , ub , lub , p) →
                record
                  { _⊑_                = LE
                  ; never              = ne
                  ; now                = n
                  ; ⨆                  = l
                  ; antisymmetry       = a
                  ; Type-UIP-unused    = u
                  ; ⊑-refl             = r
                  ; ⊑-trans            = t
                  ; never⊑             = le
                  ; upper-bound        = ub
                  ; least-upper-bound  = lub
                  ; ⊑-proof-irrelevant = p
                  }
          }
        ; right-inverse-of = λ _ → refl
        }
      ; left-inverse-of = λ _ → refl
      }

  -- Another equality characterisation lemma for
  -- Partiality-algebra-with.

  equality-characterisation-Partiality-algebra-with₂ :
    ∀ {a p q} {A : Set a} {Type : Set p}
      {P₁ P₂ : Partiality-algebra-with Type q A} →

    Propositional-extensionality q →

    let module P₁ = Partiality-algebra-with P₁
        module P₂ = Partiality-algebra-with P₂
    in
    (∃ λ (⊑⇔⊑ : ∀ x y → x P₁.⊑ y ⇔ x P₂.⊑ y) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡ P₂.⨆ (Σ-map id (_⇔_.to (⊑⇔⊑ _ _) ∘_) s))
      ↔
    P₁ ≡ P₂
  equality-characterisation-Partiality-algebra-with₂
    {q = q} {A} {Type} {P₁} {P₂} prop-ext =

    (∃ λ (⊑⇔⊑ : ∀ x y → x P₁.⊑ y ⇔ x P₂.⊑ y) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡ P₂.⨆ (Σ-map id (_⇔_.to (⊑⇔⊑ _ _) ∘_) s))  ↝⟨ Σ-cong (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                             Eq.⇔↔≃ ext P₁.⊑-propositional P₂.⊑-propositional)
                                                                          (λ _ → F.id) ⟩
    (∃ λ (⊑≃⊑ : ∀ x y → (x P₁.⊑ y) ≃ (x P₂.⊑ y)) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡ P₂.⨆ (Σ-map id (_≃_.to (⊑≃⊑ _ _) ∘_) s))  ↝⟨ inverse $ Σ-cong
                                                                     (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                        ≡≃≃ (_≃_.to
                                                                               (Propositional-extensionality-is-univalence-for-propositions
                                                                                  ext)
                                                                               prop-ext
                                                                               P₁.⊑-propositional
                                                                               P₂.⊑-propositional))
                                                                     (λ _ → F.id) ⟩
    (∃ λ (⊑≡⊑ : ∀ x y → (x P₁.⊑ y) ≡ (x P₂.⊑ y)) →
       P₁.never ≡ P₂.never
         ×
       (∀ x → P₁.now x ≡ P₂.now x)
         ×
       ∀ s → P₁.⨆ s ≡ P₂.⨆ (Σ-map id (≡⇒→ (⊑≡⊑ _ _) ∘_) s))     ↝⟨ equality-characterisation-Partiality-algebra-with₁ ⟩□

    P₁ ≡ P₂                                                     □
    where
    module P₁ = Partiality-algebra-with P₁
    module P₂ = Partiality-algebra-with P₂

------------------------------------------------------------------------
-- Partiality algebra categories

-- Partiality algebras (with fixed levels and types) form
-- precategories.

precategory :
  ∀ {a} p q (A : Set a) → Precategory (a ⊔ lsuc (p ⊔ q)) (a ⊔ p ⊔ q)
Precategory.precategory (precategory p q A) =
    Partiality-algebra p q A
  , (λ P Q → Morphism P Q , Morphism-set)
  , PA.id
  , PA._∘_
  , _↔_.to equality-characterisation-Morphism refl
  , _↔_.to equality-characterisation-Morphism refl
  , _↔_.to equality-characterisation-Morphism refl

-- A "standard notion of structure" built using
-- Partiality-algebra-with (and propositional extensionality).

standard-notion-of-structure :
  ∀ {a} p {q} (A : Set a) →
  Propositional-extensionality q →
  Standard-notion-of-structure _ _ (precategory-Set p ext)
standard-notion-of-structure p {q} A prop-ext = record
  { P               = λ B → Partiality-algebra-with (proj₁ B) q A
  ; H               = Is-morphism-with
  ; H-prop          = λ { {p = P} {q = Q} _ →
                          Is-morphism-with-propositional P Q
                        }
  ; H-id            = λ { {p = P} →
                          proj₂ $
                            _↔_.to Morphism↔Morphism-as-Σ
                              (PA.id {P = ⟨ P ⟩})
                        }
  ; H-∘             = λ { {p = P} {q = Q} {r = R}
                          f-morphism g-morphism →
                          proj₂ $
                            _↔_.to Morphism↔Morphism-as-Σ
                              (_↔_.from
                                 (Morphism↔Morphism-as-Σ
                                    {P₁ = ⟨ Q ⟩} {P₂ = ⟨ R ⟩})
                                 (_ , g-morphism)
                                 PA.∘
                               _↔_.from
                                 (Morphism↔Morphism-as-Σ {P₁ = ⟨ P ⟩})
                                 (_ , f-morphism))
                        }
  ; H-antisymmetric = λ P Q id-morphism-P→Q id-morphism-Q→P →
      _↔_.to
        (equality-characterisation-Partiality-algebra-with₂ prop-ext)
        ( (λ x y → record { to   = proj₁ id-morphism-P→Q
                          ; from = proj₁ id-morphism-Q→P
                          })
        , proj₁ (proj₂ id-morphism-P→Q)
        , proj₁ (proj₂ (proj₂ id-morphism-P→Q))
        , proj₂ (proj₂ (proj₂ id-morphism-P→Q))
        )
  }

abstract

  -- The precategory obtained from the standard notion of structure is
  -- equal to the direct definition above (assuming univalence).

  precategories-equal :
    ∀ {a p q} {A : Set a} →
    Univalence (a ⊔ lsuc (p ⊔ q)) →
    Univalence (a ⊔ p ⊔ q) →
    (prop-ext : Propositional-extensionality q) →
    Standard-notion-of-structure.Str
      (standard-notion-of-structure p A prop-ext)
      ≡
    precategory p q A
  precategories-equal {p = p} {q} {A} univ₁ univ₂ prop-ext =
    _↔_.to (equality-characterisation-Precategory ext univ₁ univ₂)
      ( ≃Partiality-algebra
      , (λ _ _ → Eq.↔⇒≃ $ inverse $ Morphism↔Morphism-as-Σ)
      , (λ _ → refl)
      , (λ _ _ _ _ _ → refl)
      )
    where
    ≃Partiality-algebra :
      (∃ λ (Type : SET p) → Partiality-algebra-with (proj₁ Type) q A)
        ≃
      Partiality-algebra p q A
    ≃Partiality-algebra =
      (∃ λ (Type : SET p) → Partiality-algebra-with (proj₁ Type) q A)  ↔⟨ inverse Σ-assoc ⟩

      (∃ λ (Type : Set p) →
         Is-set Type × Partiality-algebra-with Type q A)               ↔⟨ ∃-cong (λ _ → drop-⊤-left-× λ P → _⇔_.to contractible⇔↔⊤ $
                                                                            propositional⇒inhabited⇒contractible
                                                                              (H-level-propositional ext 2)
                                                                              (Partiality-algebra-with.Type-is-set P)) ⟩
      (∃ λ (Type : Set p) → Partiality-algebra-with Type q A)          ↝⟨ Eq.↔⇒≃ record
                                                                            { surjection = record
                                                                              { logical-equivalence = record
                                                                                { to   = uncurry λ _ P → ⟨ P ⟩
                                                                                ; from = λ P → Type P , partiality-algebra-with P
                                                                                }
                                                                              ; right-inverse-of = λ _ → refl
                                                                              }
                                                                            ; left-inverse-of = λ _ → refl
                                                                            } ⟩□
      Partiality-algebra p q A                                         □
      where
      open Partiality-algebra

-- Thus the precategory is a category (assuming univalence and
-- propositional extensionality).

category :
  ∀ {a p q} (A : Set a) →
  Univalence (a ⊔ lsuc (p ⊔ q)) →
  Univalence (a ⊔ p ⊔ q) →
  Univalence p →
  Propositional-extensionality q →
  Category (a ⊔ lsuc (p ⊔ q)) (a ⊔ p ⊔ q)
Category.category (category A univ₁ univ₂ univ₃ prop-ext) =
    precategory _ _ A
  , subst (λ C → ∀ {P Q} → Eq.Is-equivalence
                             (Precategory.≡→≅ C {P} {Q}))
          (precategories-equal univ₁ univ₂ prop-ext)
          (structure-identity-principle
             ext
             (category-Set _ ext (λ _ _ → univ₃))
             (standard-notion-of-structure _ A prop-ext))

private

  precategory-category :
    ∀ {a p} {q} {A : Set a}
      {univ₁ : Univalence (a ⊔ lsuc (p ⊔ q))}
      {univ₂ : Univalence (a ⊔ p ⊔ q)}
      {univ₃ : Univalence p}
      {prop-ext : Propositional-extensionality q} →
    Category.precategory (category A univ₁ univ₂ univ₃ prop-ext) ≡
    precategory p q A
  precategory-category = refl
