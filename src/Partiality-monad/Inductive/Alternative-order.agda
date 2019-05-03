------------------------------------------------------------------------
-- An alternative characterisation of the information ordering, along
-- with related results
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Partiality-monad.Inductive.Alternative-order
         {a} {A : Set a} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Double-negation equality-with-J as DN
open import Equality.Path.Isomorphisms equality-with-J
  using (ext; ⟨ext⟩; prop-ext)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-J as Trunc
open import Monad equality-with-J
open import Nat equality-with-J
open import Univalence-axiom equality-with-J

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Eliminators

------------------------------------------------------------------------
-- An alternative characterisation of λ x y → now x ⊑ y

-- This characterisation uses a technique from the first edition of
-- the HoTT book (Theorems 11.3.16 and 11.3.32).
--
-- The characterisation was developed together with Paolo Capriotti.

-- A binary relation, defined using structural recursion.

private

  now[_]≲-args : A → Arguments-nd (lsuc a) a A
  now[ x ]≲-args = record
    { P  = Proposition a
    ; Q  = λ P Q → proj₁ P → proj₁ Q
    ; pe = Prelude.⊥ , ⊥-propositional
    ; po = λ y → ∥ x ≡ y ∥ , truncation-is-proposition
    ; pl = λ { s (now-x≲s[_] , _) → ∥ ∃ (λ n → proj₁ (now-x≲s[ n ])) ∥
                                  , truncation-is-proposition
             }
    ; pa = λ now-x≲y now-x≲z now-x≲y→now-x≲z now-x≲z→now-x≲y →
                                            $⟨ record { to = now-x≲y→now-x≲z; from = now-x≲z→now-x≲y } ⟩
             proj₁ now-x≲y ⇔ proj₁ now-x≲z  ↝⟨ _↔_.to (⇔↔≡″ ext prop-ext) ⟩□
             now-x≲y ≡ now-x≲z              □
    ; ps = ps
    ; qr = λ { _ (now-x≲y , _) →
               now-x≲y  ↝⟨ id ⟩□
               now-x≲y  □
             }
    ; qt = λ { _ _ (P , _) (Q , _) (R , _) P→Q Q→R →
               P  ↝⟨ P→Q ⟩
               Q  ↝⟨ Q→R ⟩□
               R  □
             }
    ; qe = λ { _ (now-x≲⊥ , _) →
               Prelude.⊥  ↝⟨ ⊥-elim ⟩□
               now-x≲⊥    □
             }
    ; qu = λ { s (now-x≲s[_] , _) n →
               proj₁ now-x≲s[ n ]                ↝⟨ ∣_∣ ∘ (n ,_) ⟩□
               ∥ ∃ (λ n → proj₁ now-x≲s[ n ]) ∥  □
             }
    ; ql = λ { s ub is-ub (now-x≲s[_] , _) now-x≲ub now-x≲s[]→now-x≲ub →
               ∥ ∃ (λ n → proj₁ now-x≲s[ n ]) ∥  ↝⟨ Trunc.rec (proj₂ now-x≲ub) (uncurry now-x≲s[]→now-x≲ub) ⟩□
               proj₁ now-x≲ub                    □
             }
    ; qp = λ _ now-x≲z → Π-closure ext 1 λ _ →
                         proj₂ now-x≲z
    }
    where
    abstract
      ps : Is-set (Proposition a)
      ps = Is-set-∃-Is-proposition ext prop-ext

infix 4 now[_]≲_

now[_]≲_ : A → A ⊥ → Set a
now[ x ]≲ y = proj₁ (⊥-rec-nd now[ x ]≲-args y)

-- The relation is propositional.

now[]≲-propositional : ∀ {x y} → Is-proposition (now[ x ]≲ y)
now[]≲-propositional = proj₂ (⊥-rec-nd now[ _ ]≲-args _)

-- If a computation terminates with a certain value, then all larger
-- computations terminate with the same value (according to now[_]≲_).

larger-terminate-with-same-value≲ :
  ∀ {x y} → x ⊑ y → ∀ {z} → now[ z ]≲ x → now[ z ]≲ y
larger-terminate-with-same-value≲ x⊑y =
  ⊑-rec-nd now[ _ ]≲-args x⊑y

-- "Evaluation" lemmas for now[_]≲_.

now[]≲never : ∀ {x} → (now[ x ]≲ never) ≡ Prelude.⊥
now[]≲never {x} =
  now[ x ]≲ never  ≡⟨ cong proj₁ (⊥-rec-nd-never now[ x ]≲-args) ⟩∎
  Prelude.⊥        ∎

now[]≲now : ∀ {x y} → (now[ x ]≲ now y) ≡ ∥ x ≡ y ∥
now[]≲now {x} {y} =
  now[ x ]≲ now y  ≡⟨ cong proj₁ (⊥-rec-nd-now now[ x ]≲-args y) ⟩∎
  ∥ x ≡ y ∥        ∎

now[]≲⨆ : ∀ {x s} → (now[ x ]≲ ⨆ s) ≡ ∥ (∃ λ n → now[ x ]≲ s [ n ]) ∥
now[]≲⨆ {x} {s} =
  now[ x ]≲ ⨆ s                    ≡⟨ cong proj₁ (⊥-rec-nd-⨆ now[ x ]≲-args s) ⟩∎
  ∥ (∃ λ n → now[ x ]≲ s [ n ]) ∥  ∎

-- now[_]≲_ is pointwise equivalent to λ x y → now x ⊑ y.

now⊑≃now[]≲ : ∀ {x y} → (now x ⊑ y) ≃ (now[ x ]≲ y)
now⊑≃now[]≲ {x} {y} =
  _↔_.to (Eq.⇔↔≃ ext ⊑-propositional now[]≲-propositional)
    (record { to   = now x ⊑ y                                ↝⟨ larger-terminate-with-same-value≲ ⟩
                     (∀ {z} → now[ z ]≲ now x → now[ z ]≲ y)  ↝⟨ (λ hyp {_} eq → hyp (≡⇒→ (sym now[]≲now) eq)) ⟩
                     (∀ {z} → ∥ z ≡ x ∥ → now[ z ]≲ y)        ↝⟨ (λ hyp → hyp ∣ refl ∣) ⟩□
                     now[ x ]≲ y                              □
            ; from = ⊥-rec-⊥ from-args _
            })
  where
  from-args : Arguments-⊥ a A
  from-args = record
    { P  = λ y → now[ x ]≲ y → now x ⊑ y
    ; pe = now[ x ]≲ never  ↝⟨ ≡⇒↝ _ now[]≲never ⟩
           Prelude.⊥        ↝⟨ ⊥-elim ⟩□
           now x ⊑ never    □
    ; po = λ y →
             now[ x ]≲ now y  ↝⟨ ≡⇒↝ _ now[]≲now ⟩

             ∥ x ≡ y ∥        ↝⟨ Trunc.rec ⊑-propositional (

               x ≡ y               ↝⟨ cong now ⟩
               now x ≡ now y       ↝⟨ flip (subst (now x ⊑_)) (⊑-refl _) ⟩□
               now x ⊑ now y       □) ⟩□

             now x ⊑ now y    □
    ; pl = λ s now-x≲s→now-x⊑s →
             now[ x ]≲ ⨆ s                    ↝⟨ ≡⇒↝ _ now[]≲⨆ ⟩

             ∥ ∃ (λ n → now[ x ]≲ s [ n ]) ∥  ↝⟨ Trunc.rec ⊑-propositional (uncurry λ n now-x≲s[n] →

               now x                               ⊑⟨ now-x≲s→now-x⊑s n now-x≲s[n] ⟩
               s [ n ]                             ⊑⟨ upper-bound s n ⟩■
               ⨆ s                                 ■) ⟩□

             now x ⊑ ⨆ s                      □
    ; pp = λ _ → Π-closure ext 1 λ _ →
                 ⊑-propositional
    }

------------------------------------------------------------------------
-- Some properties that follow from the equivalence between now[_]≲_
-- and λ x y → now x ⊑ y

-- An equivalence between "now x ⊑ never" and an empty type.
--
-- This lemma was proved together with Paolo Capriotti.

now⊑never≃⊥ : {x : A} → (now x ⊑ never) ≃ Prelude.⊥ {ℓ = a}
now⊑never≃⊥ {x} =
  now x ⊑ never    ↝⟨ now⊑≃now[]≲ ⟩
  now[ x ]≲ never  ↝⟨ ≡⇒↝ _ now[]≲never ⟩□
  Prelude.⊥        □

-- Defined values of the form now x are never smaller than or equal to
-- never.
--
-- This lemma was proved together with Paolo Capriotti.

now⋢never : (x : A) → ¬ now x ⊑ never
now⋢never x =
  now x ⊑ never  ↔⟨ now⊑never≃⊥ ⟩
  Prelude.⊥      ↝⟨ ⊥-elim ⟩□
  ⊥₀             □

-- Defined values of the form now x are never equal to never.

now≢never : (x : A) → now x ≢ never
now≢never x =
  now x ≡ never                  ↝⟨ _≃_.from equality-characterisation-⊥ ⟩
  now x ⊑ never × now x ⊒ never  ↝⟨ proj₁ ⟩
  now x ⊑ never                  ↝⟨ now⋢never x ⟩□
  ⊥₀                             □

-- There is an equivalence between "now x is smaller than or equal
-- to now y" and "x is merely equal to y".

now⊑now≃∥≡∥ : {x y : A} → (now x ⊑ now y) ≃ ∥ x ≡ y ∥
now⊑now≃∥≡∥ {x} {y} =
  now x ⊑ now y    ↝⟨ now⊑≃now[]≲ ⟩
  now[ x ]≲ now y  ↝⟨ ≡⇒↝ _ now[]≲now ⟩□
  ∥ x ≡ y ∥        □

-- There is an equivalence between "now x is equal to now y" and "x
-- is merely equal to y".

now≡now≃∥≡∥ : {x y : A} → (now x ≡ now y) ≃ ∥ x ≡ y ∥
now≡now≃∥≡∥ {x} {y} =
  now x ≡ now y                  ↝⟨ inverse equality-characterisation-⊥ ⟩
  now x ⊑ now y × now x ⊒ now y  ↝⟨ now⊑now≃∥≡∥ ×-cong now⊑now≃∥≡∥ ⟩
  ∥ x ≡ y ∥ × ∥ y ≡ x ∥          ↝⟨ _↔_.to (Eq.⇔↔≃ ext (×-closure 1 truncation-is-proposition
                                                                    truncation-is-proposition)
                                                       truncation-is-proposition)
                                           (record { to = proj₁
                                                   ; from = λ ∥x≡y∥ → ∥x≡y∥ , ∥∥-map sym ∥x≡y∥
                                                   }) ⟩□
  ∥ x ≡ y ∥                      □

-- There is an equivalence between "now x is smaller than or equal to
-- now y" and "now x is equal to now y".

now⊑now≃now≡now : {x y : A} → (now x ⊑ now y) ≃ (now x ≡ now y)
now⊑now≃now≡now {x} {y} =
  now x ⊑ now y  ↝⟨ now⊑now≃∥≡∥ ⟩
  ∥ x ≡ y ∥      ↝⟨ inverse now≡now≃∥≡∥ ⟩□
  now x ≡ now y  □

-- A computation can terminate with at most one value.

termination-value-merely-unique :
  ∀ {x y z} → x ⇓ y → x ⇓ z → ∥ y ≡ z ∥
termination-value-merely-unique {x} {y} {z} x⇓y x⇓z =
  _≃_.to now≡now≃∥≡∥ (
    now y  ≡⟨ sym x⇓y ⟩
    x      ≡⟨ x⇓z ⟩∎
    now z  ∎)

-- There is an equivalence between now x ⊑ ⨆ s and
-- ∥ ∃ (λ n → now x ⊑ s [ n ]) ∥.

now⊑⨆≃∥∃now⊑∥ :
  ∀ {s : Increasing-sequence A} {x} →
  (now x ⊑ ⨆ s) ≃ ∥ ∃ (λ n → now x ⊑ s [ n ]) ∥
now⊑⨆≃∥∃now⊑∥ {s} {x} =
  now x ⊑ ⨆ s                      ↝⟨ now⊑≃now[]≲ ⟩
  now[ x ]≲ ⨆ s                    ↝⟨ ≡⇒↝ _ now[]≲⨆ ⟩
  ∥ (∃ λ n → now[ x ]≲ s [ n ]) ∥  ↝⟨ ∥∥-cong (∃-cong λ _ → inverse now⊑≃now[]≲) ⟩□
  ∥ (∃ λ n → now x ⊑ s [ n ]) ∥    □

-- If x is larger than or equal to now y, then x is equal to now y.

now⊑→⇓ : ∀ {x} {y : A} → now y ⊑ x → x ⇓ y
now⊑→⇓ {x} {y} = ⊥-rec-⊥ (record
  { P  = λ x → now y ⊑ x → x ⇓ y
  ; pe = now y ⊑ never  ↝⟨ now⋢never y ⟩
         Prelude.⊥      ↝⟨ ⊥-elim ⟩□
         never ≡ now y  □
  ; po = λ x →
           now y ⊑ now x  ↔⟨ now⊑now≃∥≡∥ ⟩
           ∥ y ≡ x ∥      ↝⟨ ∥∥-map sym ⟩
           ∥ x ≡ y ∥      ↝⟨ Trunc.rec (⊥-is-set _ _) (cong now) ⟩□
           now x ≡ now y  □
  ; pl = λ s hyp →
           now y ⊑ ⨆ s                                  ↝⟨ (λ p → p , _≃_.to now⊑⨆≃∥∃now⊑∥ p) ⟩
           now y ⊑ ⨆ s × ∥ (∃ λ n → now y ⊑ s [ n ]) ∥  ↝⟨ uncurry (λ p → Trunc.rec (⊥-is-set _ _) (uncurry λ n →

               now y ⊑ s [ n ]                               ↝⟨ (λ now⊑ _ n≤m → ⊑-trans now⊑ (later-larger s n≤m)) ⟩
               (∀ m → n ≤ m → now y ⊑ s [ m ])               ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → hyp _) ⟩
               (∀ m → n ≤ m → s [ m ] ≡ now y)               ↝⟨ (∀-cong _ λ _ → ∀-cong _ λ _ → flip (subst (_ ⊑_)) (⊑-refl _)) ⟩
               (∀ m → n ≤ m → s [ m ] ⊑ now y)               ↝⟨ upper-bound-≤→upper-bound s ⟩
               (∀ n → s [ n ] ⊑ now y)                       ↝⟨ least-upper-bound _ _ ⟩
               ⨆ s ⊑ now y                                   ↝⟨ flip antisymmetry p ⟩□
               ⨆ s ≡ now y                                   □)) ⟩□

           ⨆ s ≡ now y                                  □
  ; pp = λ _ → Π-closure ext 1 λ _ →
               ⊥-is-set _ _
  })
  x

-- If a computation terminates with a certain value, then all larger
-- computations terminate with the same value.
--
-- Capretta proved a similar result in "General Recursion via
-- Coinductive Types".

larger-terminate-with-same-value : {x y : A ⊥} → x ⊑ y → x ≼ y
larger-terminate-with-same-value now-x⊑y _ refl = now⊑→⇓ now-x⊑y

-- If one element in an increasing sequence terminates with a given
-- value, then this value is the sequence's least upper bound.

terminating-element-is-⨆ :
  ∀ (s : Increasing-sequence A) {n x} →
  s [ n ] ⇓ x → ⨆ s ⇓ x
terminating-element-is-⨆ s {n} {x} =
  larger-terminate-with-same-value (upper-bound s n) x

-- The relation _≼_ is contained in _⊑_.
--
-- Capretta proved a similar result in "General Recursion via
-- Coinductive Types".

≼→⊑ : {x y : A ⊥} → x ≼ y → x ⊑ y
≼→⊑ {x} {y} = ⊥-rec-⊥
  (record
     { P  = λ x → x ≼ y → x ⊑ y
     ; pe = never ≼ y  ↝⟨ (λ _ → never⊑ y) ⟩□
            never ⊑ y   □
     ; po = λ x →
              now x ≼ y              ↝⟨ (λ hyp → hyp x refl) ⟩
              y ⇓ x                  ↔⟨ inverse equality-characterisation-⊥ ⟩
              y ⊑ now x × y ⊒ now x  ↝⟨ proj₂ ⟩□
              now x ⊑ y              □
     ; pl = λ s s≼y→s⊑y →
              ⨆ s ≼ y                        ↝⟨ id ⟩
              (∀ z → ⨆ s ⇓ z → y ⇓ z)        ↝⟨ (λ hyp n z →

                s [ n ] ⇓ z                       ↝⟨ larger-terminate-with-same-value (upper-bound s n) z ⟩
                ⨆ s ⇓ z                           ↝⟨ hyp z ⟩□
                y ⇓ z                             □) ⟩

              (∀ n z → s [ n ] ⇓ z → y ⇓ z)  ↝⟨ id ⟩
              (∀ n → s [ n ] ≼ y)            ↝⟨ (λ hyp n → s≼y→s⊑y n (hyp n)) ⟩
              (∀ n → s [ n ] ⊑ y)            ↝⟨ least-upper-bound s y ⟩□
              ⨆ s ⊑ y                        □
     ; pp = λ _ →
              Π-closure ext 1 λ _ →
              ⊑-propositional
     })
  x

-- The two relations _≼_ and _⊑_ are pointwise equivalent.
--
-- Capretta proved a similar result in "General Recursion via
-- Coinductive Types".

≼≃⊑ : {x y : A ⊥} → (x ≼ y) ≃ (x ⊑ y)
≼≃⊑ = _↔_.to (Eq.⇔↔≃ ext ≼-propositional ⊑-propositional)
             (record { to   = ≼→⊑
                     ; from = larger-terminate-with-same-value
                     })

-- An alternative characterisation of _⇓_.

⇓≃now⊑ : ∀ {x} {y : A} → (x ⇓ y) ≃ (now y ⊑ x)
⇓≃now⊑ {x} {y} =
  _↔_.to (Eq.⇔↔≃ ext (⊥-is-set _ _) ⊑-propositional) (record
    { to   = x ≡ now y              ↔⟨ inverse equality-characterisation-⊥ ⟩
             x ⊑ now y × x ⊒ now y  ↝⟨ proj₂ ⟩□
             now y ⊑ x              □
    ; from = now y ⊑ x                  ↝⟨ larger-terminate-with-same-value ⟩
             (∀ z → now y ⇓ z → x ⇓ z)  ↝⟨ (λ hyp → hyp y refl) ⟩□
             x ⇓ y                      □
    })

-- Another alternative characterisation of _⇓_.

⇓≃now[]≲ : ∀ {x y} → (x ⇓ y) ≃ (now[ y ]≲ x)
⇓≃now[]≲ {x} {y} =
  x ⇓ y        ↝⟨ ⇓≃now⊑ ⟩
  now y ⊑ x    ↝⟨ now⊑≃now[]≲ ⟩□
  now[ y ]≲ x  □

-- Two corollaries of ⇓≃now[]≲.

never⇓≃⊥ : {x : A} → (never ⇓ x) ≃ Prelude.⊥ {ℓ = a}
never⇓≃⊥ {x = x} =
  never ≡ now x    ↝⟨ ⇓≃now[]≲ ⟩
  now[ x ]≲ never  ↝⟨ ≡⇒↝ _ now[]≲never ⟩□
  Prelude.⊥        □

⨆⇓≃∥∃⇓∥ :
  ∀ {s : Increasing-sequence A} {x} →
  (⨆ s ⇓ x) ≃ ∥ ∃ (λ n → s [ n ] ⇓ x) ∥
⨆⇓≃∥∃⇓∥ {s} {x} =
  ⨆ s ⇓ x                          ↝⟨ ⇓≃now[]≲ ⟩
  now[ x ]≲ ⨆ s                    ↝⟨ ≡⇒↝ _ now[]≲⨆ ⟩
  ∥ ∃ (λ n → now[ x ]≲ s [ n ]) ∥  ↝⟨ ∥∥-cong (∃-cong λ _ → inverse ⇓≃now[]≲) ⟩□
  ∥ ∃ (λ n → s [ n ] ⇓ x) ∥        □

-- If x does not terminate, then x is equal to never.

¬⇓→⇑ : {x : A ⊥} → ¬ (∃ λ y → x ⇓ y) → x ⇑
¬⇓→⇑ {x} = ⊥-rec-⊥
  (record
     { P  = λ x → ¬ (∃ λ y → x ⇓ y) → x ⇑
     ; pe = ¬ ∃ (never ⇓_)  ↝⟨ const refl ⟩□
            never ⇑         □
     ; po = λ x →
              ¬ ∃ (now x ⇓_) ↝⟨ _$ (x , refl) ⟩
              ⊥₀             ↝⟨ ⊥-elim ⟩□
              now x ⇑        □
     ; pl = λ s ih →
              ¬ ∃ (⨆ s ⇓_)                           ↔⟨ →-cong ext (∃-cong (λ _ → ⨆⇓≃∥∃⇓∥)) F.id ⟩
              ¬ ∃ (λ x → ∥ ∃ (λ n → s [ n ] ⇓ x) ∥)  ↝⟨ (λ { hyp (n , x , s[n]⇓x) → hyp (x , ∣ n , s[n]⇓x ∣) }) ⟩
              ¬ ∃ (λ n → ∃ λ x → s [ n ] ⇓ x)        ↝⟨ (λ hyp n → ih n (hyp ∘ (n ,_))) ⟩
              (∀ n → s [ n ] ⇑)                      ↝⟨ sym ∘ _↔_.to equality-characterisation-increasing ⟩
              constˢ never ≡ s                       ↝⟨ flip (subst (λ s → ⨆ s ⇑)) ⨆-const ⟩□
              ⨆ s ⇑                                  □
     ; pp = λ _ → Π-closure ext 1 λ _ →
                  ⊥-is-set _ _
     })
  x

-- In the double-negation monad a computation is either terminating or
-- non-terminating.

now-or-never : (x : A ⊥) → ¬ ¬ ((∃ λ y → x ⇓ y) ⊎ x ⇑)
now-or-never x = run (map (⊎-map id ¬⇓→⇑) excluded-middle)

-- _⊑_ is a flat order, in the sense that distinct elements that are
-- distinct from never are unrelated.

flat-order : {x y : A ⊥} → x ≢ y → ¬ x ⇑ → ¬ y ⇑ → ¬ (x ⊑ y)
flat-order {x} {y} x≢y never≢x never≢y x⊑y = ¬¬¬⊥ $
  ¬⇑→¬¬⇓ never≢x >>= λ x⇓ →
  ¬⇑→¬¬⇓ never≢y >>= λ y⇓ →
  return (⊥-elim $ ¬x⇓×y⇓ (x⇓ , y⇓))
  where
  -- The computations x and y cannot both terminate.

  ¬x⇓×y⇓ : ¬ ((∃ λ z → x ⇓ z) × (∃ λ z → y ⇓ z))
  ¬x⇓×y⇓ ((xz , refl) , (yz , refl)) = x≢y (
    now xz      ≡⟨ _≃_.to now⊑now≃now≡now (

        now xz       ⊑⟨ x⊑y ⟩■
        now yz       ■) ⟩∎

    now yz      ∎)

  -- Computations that fail to be equal to never do not fail to
  -- terminate.

  ¬⇑→¬¬⇓ : {x : A ⊥} → ¬ x ⇑ → ¬¬ (∃ λ y → x ⇓ y)
  run (¬⇑→¬¬⇓ ¬x⇑) = ¬x⇑ ∘ ¬⇓→⇑

-- Some "constructors" for □.

□-never :
  ∀ {ℓ} {P : A → Set ℓ} →
  □ P never
□-never {P = P} y =
  never ⇓ y        ↔⟨ ⇓≃now[]≲ ⟩
  now[ y ]≲ never  ↔⟨ ≡⇒↝ bijection now[]≲never ⟩
  Prelude.⊥        ↝⟨ ⊥-elim ⟩□
  P y              □

□-now :
  ∀ {ℓ} {P : A → Set ℓ} {x} →
  Is-proposition (P x) →
  P x → □ P (now x)
□-now {P = P} {x} P-prop p y =
  now x ⇓ y  ↔⟨ now≡now≃∥≡∥ ⟩
  ∥ x ≡ y ∥  ↝⟨ (λ ∥x≡y∥ →
                   Trunc.rec (Trunc.rec (H-level-propositional ext 1)
                                        (λ x≡y → subst (Is-proposition ∘ P) x≡y P-prop)
                                        ∥x≡y∥)
                             (λ x≡y → subst P x≡y p)
                             ∥x≡y∥) ⟩□
  P y        □

□-⨆ :
  ∀ {ℓ} {P : A → Set ℓ} →
  (∀ x → Is-proposition (P x)) →
  ∀ {s} → (∀ n → □ P (s [ n ])) → □ P (⨆ s)
□-⨆ {P = P} P-prop {s} p y =
  ⨆ s ⇓ y                    ↔⟨ ⨆⇓≃∥∃⇓∥ ⟩
  ∥ ∃ (λ n → s [ n ] ⇓ y) ∥  ↝⟨ Trunc.rec (P-prop y) (uncurry λ n s[n]⇓y → p n y s[n]⇓y) ⟩□
  P y                        □

-- One "non-constructor" and one "constructor" for ◇.

◇-never :
  ∀ {ℓ} {P : A → Set ℓ} →
  ¬ ◇ P never
◇-never {P = P} =
  ◇ P never                      ↝⟨ id ⟩
  ∥ (∃ λ y → never ⇓ y × P y) ∥  ↝⟨ Trunc.rec ⊥-propositional (now≢never _ ∘ sym ∘ proj₁ ∘ proj₂) ⟩□
  ⊥₀                             □

◇-⨆ :
  ∀ {ℓ} {P : A → Set ℓ} →
  ∀ {s n} → ◇ P (s [ n ]) → ◇ P (⨆ s)
◇-⨆ {P = P} =
  ∥∥-map (Σ-map id (λ {x} → Σ-map {Q = λ _ → P x}
                                  (terminating-element-is-⨆ _) id))

------------------------------------------------------------------------
-- An alternative characterisation of _⊑_

-- This characterisation uses a technique from the first edition of
-- the HoTT book (Theorems 11.3.16 and 11.3.32).
--
-- The characterisation was developed together with Paolo Capriotti.

-- A binary relation, defined using structural recursion.

private

  ≲-args : Arguments-nd (lsuc a) a A
  ≲-args = record
    { P  = A ⊥ → Proposition a
    ; Q  = λ P Q → ∀ z → proj₁ (Q z) → proj₁ (P z)
    ; pe = λ _ → ↑ _ ⊤ , ↑-closure 1 (mono₁ 0 ⊤-contractible)
    ; po = λ x y → ⊥-rec-nd now[ x ]≲-args y
    ; pl = λ { _ (s[_]≲ , _) y → (∀ n → proj₁ (s[ n ]≲ y))
                               , Π-closure ext 1 λ n →
                                 proj₂ (s[ n ]≲ y)
             }
    ; pa = λ x≲ y≲ y≲→x≲ x≲→y≲ → ⟨ext⟩ λ z →
                                          $⟨ record { to = x≲→y≲ z; from = y≲→x≲ z } ⟩
             proj₁ (x≲ z) ⇔ proj₁ (y≲ z)  ↝⟨ _↔_.to (⇔↔≡″ ext prop-ext) ⟩□
             x≲ z ≡ y≲ z                  □
    ; ps = ps
    ; qr = λ _ x≲ z →
             proj₁ (x≲ z)  ↝⟨ id ⟩□
             proj₁ (x≲ z)  □
    ; qt = λ _ _ P Q R Q→P R→Q z →
             proj₁ (R z)  ↝⟨ R→Q z ⟩
             proj₁ (Q z)  ↝⟨ Q→P z ⟩□
             proj₁ (P z)  □
    ; qe = λ _ ⊥≲ z →
             proj₁ (⊥≲ z)  ↝⟨ _ ⟩□
             ↑ _ ⊤         □
    ; qu = λ { s (s[_]≲ , _) n z →
               (∀ m → proj₁ (s[ m ]≲ z))  ↝⟨ (_$ n) ⟩□
               proj₁ (s[ n ]≲ z)          □
             }
    ; ql = λ { _ _ _ (s[_]≲ , _) ub≲ ub≲→s[]≲ z →
               proj₁ (ub≲ z)              ↝⟨ flip (flip ub≲→s[]≲ z) ⟩□
               (∀ n → proj₁ (s[ n ]≲ z))  □
             }
    ; qp = λ x≲ y≲ → Π-closure ext 1 λ z →
                     Π-closure ext 1 λ _ →
                     proj₂ (x≲ z)
    }
    where
    abstract
      ps : Is-set (A ⊥ → Proposition a)
      ps =
        Π-closure ext 2 λ _ →
        Is-set-∃-Is-proposition ext prop-ext

infix 4 _≲_

_≲_ : A ⊥ → A ⊥ → Set a
x ≲ y = proj₁ (⊥-rec-nd ≲-args x y)

-- The relation is propositional.

≲-propositional : ∀ x y → Is-proposition (x ≲ y)
≲-propositional x y = proj₂ (⊥-rec-nd ≲-args x y)

-- A form of transitivity involving _⊑_ and _≲_.

⊑≲-trans : ∀ {x y} (z : A ⊥) → x ⊑ y → y ≲ z → x ≲ z
⊑≲-trans z x⊑y = ⊑-rec-nd ≲-args x⊑y z

-- "Evaluation" lemmas for _≲_.

never≲ : ∀ {y} → (never ≲ y) ≡ ↑ _ ⊤
never≲ {y} = cong (proj₁ ∘ (_$ _)) (
  ⊥-rec-nd ≲-args never  ≡⟨ ⊥-rec-nd-never ≲-args ⟩∎
  (λ _ → ↑ _ ⊤ , _)      ∎)

⨆≲ : ∀ {s y} → (⨆ s ≲ y) ≡ ∀ n → s [ n ] ≲ y
⨆≲ {s} {y} = cong (proj₁ ∘ (_$ _)) (
  ⊥-rec-nd ≲-args (⨆ s)            ≡⟨ ⊥-rec-nd-⨆ ≲-args s ⟩∎
  (λ y → (∀ n → s [ n ] ≲ y) , _)  ∎)

now≲ : ∀ {x y} → (now x ≲ y) ≡ (now[ x ]≲ y)
now≲ {x} {y} =
  now x ≲ y    ≡⟨ cong (proj₁ ∘ (_$ _)) (⊥-rec-nd-now ≲-args x) ⟩∎
  now[ x ]≲ y  ∎

now≲never : ∀ {x} → (now x ≲ never) ≡ Prelude.⊥
now≲never {x} =
  now x ≲ never    ≡⟨ now≲ ⟩
  now[ x ]≲ never  ≡⟨ now[]≲never ⟩∎
  Prelude.⊥        ∎

now≲now : ∀ {x y} → (now x ≲ now y) ≡ ∥ x ≡ y ∥
now≲now {x} {y} =
  now x ≲ now y    ≡⟨ now≲ ⟩
  now[ x ]≲ now y  ≡⟨ now[]≲now ⟩∎
  ∥ x ≡ y ∥        ∎

now≲⨆ : ∀ {x s} → (now x ≲ ⨆ s) ≡ ∥ (∃ λ n → now x ≲ s [ n ]) ∥
now≲⨆ {x} {s} =
  now x ≲ ⨆ s                      ≡⟨ now≲ ⟩
  now[ x ]≲ ⨆ s                    ≡⟨ now[]≲⨆ ⟩
  ∥ (∃ λ n → now[ x ]≲ s [ n ]) ∥  ≡⟨ cong (∥_∥ ∘ ∃) (⟨ext⟩ λ _ → sym now≲) ⟩∎
  ∥ (∃ λ n → now x ≲ s [ n ]) ∥    ∎

-- _≲_ is reflexive.

≲-refl : ∀ x → x ≲ x
≲-refl = ⊥-rec-⊥ (record
  { pe =                $⟨ _ ⟩
         ↑ _ ⊤          ↝⟨ ≡⇒↝ bijection $ sym never≲ ⟩□
         never ≲ never  □
  ; po = λ x →            $⟨ ∣ refl ∣ ⟩
           ∥ x ≡ x ∥      ↝⟨ ≡⇒↝ bijection $ sym now≲now ⟩□
           now x ≲ now x  □
  ; pl = λ s →
           (∀ n → s [ n ] ≲ s [ n ])  ↝⟨ (λ s≲s n → ⨆-lemma s (s [ n ]) n (s≲s n)) ⟩
           (∀ n → s [ n ] ≲ ⨆ s)      ↔⟨ ≡⇒↝ bijection $ sym ⨆≲ ⟩□
           ⨆ s ≲ ⨆ s                  □
  ; pp = λ x → ≲-propositional x x
  })
  where
  ⨆-lemma : ∀ s x n → x ≲ s [ n ] → x ≲ ⨆ s
  ⨆-lemma s = ⊥-rec-⊥
    (record
       { P  = λ x → ∀ n → x ≲ s [ n ] → x ≲ ⨆ s
       ; pe = λ n →
                never ≲ s [ n ]  ↔⟨ ≡⇒↝ bijection $ never≲ ⟩
                ↑ _ ⊤            ↔⟨ ≡⇒↝ bijection $ sym never≲ ⟩□
                never ≲ ⨆ s      □
       ; po = λ x n →
                now x ≲ s [ n ]                ↝⟨ ∣_∣ ∘ (n ,_) ⟩
                ∥ (∃ λ n → now x ≲ s [ n ]) ∥  ↔⟨ ≡⇒↝ bijection $ sym now≲⨆ ⟩□
                now x ≲ ⨆ s                    □
       ; pl = λ s′ →
                (∀ m n → s′ [ m ] ≲ s [ n ] → s′ [ m ] ≲ ⨆ s)  ↝⟨ (λ hyp n s′≲s m → hyp m n (s′≲s m)) ⟩

                (∀ n → (∀ m → s′ [ m ] ≲ s [ n ]) →
                       (∀ m → s′ [ m ] ≲ ⨆ s))                 ↝⟨ ∀-cong _ (λ _ →
                                                                    ≡⇒↝ _ $ sym $ cong₂ (λ x y → x → y) ⨆≲ ⨆≲) ⟩□
                (∀ n → ⨆ s′ ≲ s [ n ] → ⨆ s′ ≲ ⨆ s)            □
       ; pp = λ x → Π-closure ext 1 λ _ →
                    Π-closure ext 1 λ _ →
                    ≲-propositional x (⨆ s)
       })

-- _⊑_ and _≲_ are pointwise equivalent.

⊑≃≲ : ∀ {x y} → (x ⊑ y) ≃ (x ≲ y)
⊑≃≲ {x} {y} =
  _↔_.to (Eq.⇔↔≃ ext ⊑-propositional (≲-propositional x y))
    (record { to   = λ x⊑y → ⊑≲-trans _ x⊑y (≲-refl y)
            ; from = ⊥-rec-⊥ from-args _ _
            })
  where
  from-args : Arguments-⊥ a A
  from-args = record
    { P  = λ x → ∀ y → x ≲ y → x ⊑ y
    ; pe = λ y _ → never⊑ y
    ; po = λ x y →
             now x ≲ y    ↝⟨ ≡⇒↝ _ now≲ ⟩
             now[ x ]≲ y  ↔⟨ inverse now⊑≃now[]≲ ⟩□
             now x ⊑ y    □
    ; pl = λ s s≲→s⊑ y →
             ⨆ s ≲ y              ↝⟨ ≡⇒↝ _ ⨆≲ ⟩
             (∀ n → s [ n ] ≲ y)  ↝⟨ (λ s[_]≲y n → s≲→s⊑ n y s[ n ]≲y) ⟩
             (∀ n → s [ n ] ⊑ y)  ↝⟨ least-upper-bound s y ⟩□
             ⨆ s ⊑ y              □
    ; pp = λ _ → Π-closure ext 1 λ _ →
                 Π-closure ext 1 λ _ →
                 ⊑-propositional
    }
