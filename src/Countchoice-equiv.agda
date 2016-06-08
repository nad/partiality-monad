
-- Goal of this module: establish an equivalence between
-- the QIIT partiality monad and the quotiented delay monad.

{-# OPTIONS --without-K #-}

module Countchoice-equiv where

open import Prelude
open import Equality
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


  -- The goal: a function Delay A ∞ → Seq.

  -- intuition: given (x : Delay A ∞) and a number n, we try to evaluate x by removing 'laters'.
  -- We give up after n steps.
  k : ℕ → Delay A ∞ → Maybe A
  k zero    = λ { (now a)   → just a ;
                  (later _) → nothing }
  k (suc n) = λ { (now a)   → just a ;
                  (later x) → k n (force x) }

  k-lemma : (x : Delay A ∞) (n : ℕ) (a : A) → (k n x ≡ just a) → (k (suc n) x ≡ just a)
  k-lemma x zero a k₀x≡justₐ with x  
  k-lemma x zero a k₀x≡justₐ | now b = k₀x≡justₐ
  k-lemma x zero a ()        | just y
  k-lemma x (suc n) a kₙx≡justₐ with x
  k-lemma x (suc n) a kₙx≡justₐ | now b = kₙx≡justₐ
  k-lemma x (suc n) a kₙx≡justₐ | later y = k-lemma (force y) n a kₙx≡justₐ

  k-is-mon : (x : Delay A ∞) → is-monotone (λ n → k n x)
  k-is-mon x n with k n x 
  k-is-mon x n | nothing with k (suc n) x
  k-is-mon x n | nothing | nothing = inj₁ refl
  k-is-mon x n | nothing | just y  = inj₂ (refl , (λ ()))
  k-is-mon x n | just a = inj₁ (sym (k-lemma x n a {!refl!}))


  D→Seq : Delay A ∞ → Seq
  D→Seq x = (λ n → k n x) , k-is-mon x

  -- this function D→Seq SHOULD be definable in a more elegant way as follows; however, the termination checker seems to make problems because it's not clear that we do "induction on n":
  D→Seq' : Delay A ∞ → Seq
  D→Seq' (now a)   = (λ _ → just a) , (λ _ → inj₁ refl)
  D→Seq' (later y) = shift (D→Seq' {!force y!})

  -- what we can do instead is this:
  D→Seq-lem : (y : _) → D→Seq (later y) ≡ shift (D→Seq (force y))
  D→Seq-lem y = {!!}


{- doing it explicitly, not using unshift
  Seq→D : Seq → Delay A ∞
  Seq→D (f , m) with f zero
  Seq→D (f , m) | nothing = later (∞Seq→D (f , m)) where
    ∞Seq→D : Seq → ∞Delay A ∞
    force (∞Seq→D (f , m)) = Seq→D (f , m) 
  Seq→D (f , m) | just a = now a
-}

  Seq→D : Seq → Delay A ∞
  Seq→D (f , m) with f zero
  Seq→D (f , m) | nothing = later (∞Seq→D (unshift (f , m))) where
    ∞Seq→D : Seq → ∞Delay A ∞
    force (∞Seq→D (f , m)) = Seq→D (f , m) -- I have copied this from the other file ('Alternative'). I know this is what I want, but I don't know what this syntax is doing to be honest.
  Seq→D (f , m) | just a  = now a


  -- test: unshift is strictly a retraction of shift! (thanks to η for Σ)
  unshift-shift : (x : Seq) → unshift (shift x) ≡ x
  unshift-shift x = refl


  D→Set→D : (x : Delay A ∞) → Seq→D (D→Seq x) ≡ x
  D→Set→D (now a)   = refl
  D→Set→D (later y) =
    Seq→D (D→Seq (later y))
      ≡⟨ {!refl!} ⟩
    Seq→D {! (shift (D→Seq (force y))) !}
      ≡⟨ {!!} ⟩
    {! ( (Seq→D (unshift (shift (D→Seq (force y))))))!}
      ≡⟨ {!!} ⟩ 

    {!later (force (Seq→D (unshift (shift (D→Seq (force y))))))!}
      ≡⟨ {!!} ⟩
    {!!}
      ≡⟨ {!!} ⟩ 
    later y ∎ 



  Delay≃Seq : Delay A ∞ ≃ Seq -- (Delay A) ≃  Seq
  Delay≃Seq = ↔⇒≃ (record { surjection = record { logical-equivalence = record { to = {!!} ; from = {!!} } ; right-inverse-of = λ x → {!!} } ; left-inverse-of = λ x → {!!} })
