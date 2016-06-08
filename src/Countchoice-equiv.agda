


{-# OPTIONS --without-K #-}

module Countchoice-equiv where

open import Prelude
open import Equality.Propositional
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Logical-equivalence
open import Nat equality-with-J
open import Equivalence equality-with-J

open import Delay-monad


postulate
  ext : ∀ {a b} → Extensionality a b


module _ {a} {Aset : SET a} where

  A = proj₁ Aset
  A-is-set = proj₂ Aset

  MA-is-set : Is-set (Maybe A)
  MA-is-set = ⊎-closure 0 (mono₁ 1 (mono₁ 0 ⊤-contractible)) A-is-set

  -- a predicate stating that a function ℕ → Maybe A is monotone
  is-monotone : (f : ℕ → Maybe A) → Set a
  is-monotone f = (n : ℕ) → (f n ≡ f (suc n)) ⊎ f n ≡ nothing × f (suc n) ≢ nothing

  is-monotone-is-prop : (f : ℕ → Maybe A) → Is-proposition (is-monotone f) 
  is-monotone-is-prop f =
    Π-closure {A = ℕ} ext 1 (λ n → _⇔_.from propositional⇔irrelevant (λ {
      (inj₁ fn≡fSn₁) (inj₁ fn≡fSn₂) → cong inj₁ (_⇔_.to set⇔UIP MA-is-set _ _) ; 
      (inj₁ fn≡fSn) (inj₂ (fn≡nothing , fSn≢nothing)) → ⊥-elim (fSn≢nothing (trans (sym fn≡fSn) fn≡nothing)) ;
      (inj₂ (fn≡nothing , fSn≢nothing)) (inj₁ fn≡fSn) → ⊥-elim (fSn≢nothing (trans (sym fn≡fSn) fn≡nothing)) ;
      (inj₂ (fn≡nothing₁ , fSn≢nothing₁)) (inj₂ (fn≡nothing₂ , fSn≢nothing₂)) →
        cong inj₂ (Σ-≡,≡→≡ {B = λ _ → f (suc n) ≢ nothing}
                    (_⇔_.to set⇔UIP MA-is-set _ _)
                    (_⇔_.to propositional⇔irrelevant (¬-propositional ext) _ _)) }))

  Seq : Set a
  Seq = Σ (ℕ → Maybe A) is-monotone

  shift : Seq → Seq
  shift (f , m) = (λ { zero → nothing ; (suc n) → f n })
                  ,
                  (λ { zero → aux ; (suc n) → m n }) where
                    aux : nothing ≡ f 0 ⊎ (nothing ≡ nothing) × f 0 ≢ nothing
                    aux with f zero
                    aux | nothing = inj₁ refl
                    aux | just a = inj₂ (refl , (λ ()))

  unshift : Seq → Seq
  unshift (f , m) = (λ n → f (suc n)) , (λ n → m (suc n))

  _↓_ : Seq → A → Set _
  (f , m) ↓ a = Σ ℕ (λ n → f n ≡ just a × ((n' : ℕ) → (f n' ≢ nothing) → n ≤ n')) -- CAVEAT: this could possibly be nicer with <



  k : Delay A ∞ × ℕ → Maybe A
  k (now a , _) = just a
  k (later _ , zero) = nothing
  k (later x , suc n) = k ({!x!} , n)

  test : (a : A) → k ({!force!} , zero) ≡ nothing
  test = {!!}

  Delay≃Seq : Delay A ∞ ≃ Seq -- (Delay A) ≃  Seq
  Delay≃Seq = ↔⇒≃ (record { surjection = record { logical-equivalence = record { to = {!!} ; from = {!!} } ; right-inverse-of = λ x → {!!} } ; left-inverse-of = λ x → {!!} })
