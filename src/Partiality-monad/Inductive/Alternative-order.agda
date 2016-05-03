------------------------------------------------------------------------
-- An alternative characterisation of the information ordering, along
-- with related results
------------------------------------------------------------------------

{-# OPTIONS --without-K --rewriting #-}

open import Equality.Propositional
open import Univalence-axiom equality-with-J

-- The characterisation uses univalence.

module Partiality-monad.Inductive.Alternative-order
         {a} {A : Set a} (univ : Univalence a) where

open import H-level.Truncation.Propositional as Trunc
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
import Nat
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Eliminators
open import Partiality-monad.Inductive.Properties

------------------------------------------------------------------------
-- The alternative characterisation

-- This characterisation uses a technique from the first edition of
-- the HoTT book (Theorems 11.3.16 and 11.3.32).
--
-- The characterisation was developed together with Paolo Capriotti
-- and Nicolai Kraus.

-- A binary relation, defined using structural recursion.

private

  now[_]≲-args : A → Rec-args-nd A (Proposition a)
                                 (λ P Q → proj₁ P → proj₁ Q)
  now[ x ]≲-args = record
    { pe = Prelude.⊥ , ⊥-propositional
    ; po = λ y → ∥ x ≡ y ∥ , truncation-is-proposition
    ; pl = λ { s (now-x≲s[_] , _) → ∥ ∃ (λ n → proj₁ (now-x≲s[ n ])) ∥
                                  , truncation-is-proposition
             }
    ; pa = λ now-x≲y now-x≲z now-x≲y→now-x≲z now-x≲z→now-x≲y →
                                            $⟨ record { to = now-x≲y→now-x≲z; from = now-x≲z→now-x≲y } ⟩
             proj₁ now-x≲y ⇔ proj₁ now-x≲z  ↝⟨ _↔_.to (⇔↔≡′ ext univ) ⟩□
             now-x≲y ≡ now-x≲z              □
    ; qr = λ { _ (now-x≲y , _) →
               now-x≲y  ↝⟨ id ⟩□
               now-x≲y  □
             }
    ; qe = λ { _ (now-x≲⊥ , _) →
               Prelude.⊥  ↝⟨ ⊥-elim ⟩□
               now-x≲⊥    □
             }
    ; qu = λ { _ _ _ n (now-x≲s[_] , _) (now-x≲ub , _)
               now-x≲s[]→now-x≲ub →

               proj₁ now-x≲s[ n ]                ↝⟨ ∣_∣ ∘ (n ,_) ⟩
               ∥ ∃ (λ n → proj₁ now-x≲s[ n ]) ∥  ↝⟨ now-x≲s[]→now-x≲ub ⟩□
               now-x≲ub                          □
             }
    ; ql = λ { s ub is-ub (now-x≲s[_] , _) now-x≲ub now-x≲s[]→now-x≲ub →
               ∥ ∃ (λ n → proj₁ now-x≲s[ n ]) ∥  ↝⟨ Trunc.rec (proj₂ now-x≲ub) (uncurry now-x≲s[]→now-x≲ub) ⟩□
               proj₁ now-x≲ub                    □
             }
    ; qp = λ _ now-x≲z → Π-closure ext 1 λ _ →
                         proj₂ now-x≲z
    }

  ≲-args : Rec-args-nd A (A ⊥ → Proposition a)
                       (λ P Q → ∀ z → proj₁ (Q z) → proj₁ (P z))
  ≲-args = record
    { pe = λ _ → ↑ _ ⊤ , ↑-closure 1 (mono₁ 0 ⊤-contractible)
    ; po = λ x y → ⊥-rec-nd now[ x ]≲-args y
    ; pl = λ { _ (s[_]≲ , _) y → (∀ n → proj₁ (s[ n ]≲ y))
                               , Π-closure ext 1 λ n →
                                 proj₂ (s[ n ]≲ y)
             }
    ; pa = λ x≲ y≲ y≲→x≲ x≲→y≲ → ext λ z →
                                          $⟨ record { to = x≲→y≲ z; from = y≲→x≲ z } ⟩
             proj₁ (x≲ z) ⇔ proj₁ (y≲ z)  ↝⟨ _↔_.to (⇔↔≡′ ext univ) ⟩
             x≲ z ≡ y≲ z                  □
    ; qr = λ _ x≲ z →
             proj₁ (x≲ z)  ↝⟨ id ⟩□
             proj₁ (x≲ z)  □
    ; qe = λ _ ⊥≲ z →
             proj₁ (⊥≲ z)  ↝⟨ _ ⟩□
             ↑ _ ⊤         □
    ; qu = λ { _ _ _ n (s[_]≲ , _) ub≲ ub≲→s[]≲ z →
               proj₁ (ub≲ z)      ↝⟨ flip (ub≲→s[]≲ z) n ⟩□
               proj₁ (s[ n ]≲ z)  □
             }
    ; ql = λ { _ _ _ (s[_]≲ , _) ub≲ ub≲→s[]≲ z →
               proj₁ (ub≲ z)              ↝⟨ flip (flip ub≲→s[]≲ z) ⟩□
               (∀ n → proj₁ (s[ n ]≲ z))  □
             }
    ; qp = λ x≲ y≲ → Π-closure ext 1 λ z →
                     Π-closure ext 1 λ _ →
                     proj₂ (x≲ z)
    }

infix 4 _≲_

_≲_ : A ⊥ → A ⊥ → Set a
x ≲ y = proj₁ (⊥-rec-nd ≲-args x y)

-- The relation is propositional.

≲-propositional : ∀ x y → Is-proposition (x ≲ y)
≲-propositional x y = proj₂ (⊥-rec-nd ≲-args x y)

-- A form of transitivity involving _⊑_ and _≲_.

⊑≲-trans : ∀ {x y} (z : A ⊥) → x ⊑ y → y ≲ z → x ≲ z
⊑≲-trans z x⊑y = ⊑-rec-nd ≲-args x⊑y z

private

  -- Lemmas showing certain aspects of how _≲_ evaluates.

  never≲ : ∀ y → (never ≲ y) ≡ ↑ _ ⊤
  never≲ _ = refl

  ⨆≲ : ∀ s y → (⨆ s ≲ y) ≡ ∀ n → s [ n ] ≲ y
  ⨆≲ _ _ = refl

  now≲never : ∀ x → (now x ≲ never) ≡ Prelude.⊥
  now≲never _ = refl

  now≲now : ∀ x y → (now x ≲ now y) ≡ ∥ x ≡ y ∥
  now≲now _ _ = refl

  now≲⨆ : ∀ x s → (now x ≲ ⨆ s) ≡ ∥ (∃ λ n → now x ≲ s [ n ]) ∥
  now≲⨆ _ _ = refl

-- _≲_ is reflexive.

≲-refl : ∀ x → x ≲ x
≲-refl = ⊥-rec-Prop (record
  { po = λ _ → ∣ refl ∣
  ; pl = λ s →
           (∀ n → s [ n ] ≲ s [ n ])  ↝⟨ (λ s≲s n → ⨆-lemma s (s [ n ]) n (s≲s n)) ⟩
           (∀ n → s [ n ] ≲ ⨆ s)      □
  ; pp = λ x → ≲-propositional x x
  })
  where
  ⨆-lemma : ∀ s x n → x ≲ s [ n ] → x ≲ ⨆ s
  ⨆-lemma s = ⊥-rec-Prop
    {P = λ x → ∀ n → x ≲ s [ n ] → x ≲ ⨆ s}
    (record
       { po = λ x n →
                now x ≲ s [ n ]                ↝⟨ ∣_∣ ∘ (n ,_) ⟩
                ∥ (∃ λ n → now x ≲ s [ n ]) ∥  □
       ; pl = λ s′ →
                (∀ m n → s′ [ m ] ≲ s [ n ] → s′ [ m ] ≲ ⨆ s)  ↝⟨ (λ hyp n s′≲s m → hyp m n (s′≲s m)) ⟩
                (∀ n → (∀ m → s′ [ m ] ≲ s [ n ]) →
                       (∀ m → s′ [ m ] ≲ ⨆ s))                 □
       ; pp = λ x → Π-closure ext 1 λ _ →
                    Π-closure ext 1 λ _ →
                    ≲-propositional x (⨆ s)
       })

-- _⊑_ and _≲_ are pointwise equivalent.

⊑≃≲ : ∀ {x y} → (x ⊑ y) ≃ (x ≲ y)
⊑≃≲ {x} {y} =
  _↔_.to (Eq.⇔↔≃ ext ⊑-propositional (≲-propositional x y))
    (record { to   = ⊑-rec-⊑ to-args
            ; from = ⊥-rec-Prop from-args _ _
            })
  where
  to-args : Rec-args-⊑ (λ {x y} _ → x ≲ y)
  to-args = record
    { qr = λ x → ≲-refl x
    ; qu = λ s ub _ n _ ⨆s≲ub → ⨆s≲ub n
    ; ql = λ s ub _ _ s[_]≲ub n → s[ n ]≲ub
    ; qp = λ {x y} _ → ≲-propositional x y
    }

  now-lemma : ∀ x y → now x ≲ y → now x ⊑ y
  now-lemma x y = ⊥-rec-Prop
    {P = λ y → now x ≲ y → now x ⊑ y}
    (record
       { pe = Prelude.⊥      ↝⟨ ⊥-elim ⟩□
              now x ⊑ never  □
       ; po = λ y →
                ∥ x ≡ y ∥        ↝⟨ Trunc.rec ⊑-propositional (

                  x ≡ y               ↝⟨ cong now ⟩
                  now x ≡ now y       ↝⟨ flip (subst (now x ⊑_)) (⊑-refl _) ⟩□
                  now x ⊑ now y       □) ⟩□

                now x ⊑ now y    □
       ; pl = λ s now-x≲s→now-x⊑s →
                ∥ ∃ (λ n → now x ≲ s [ n ]) ∥  ↝⟨ Trunc.rec ⊑-propositional (uncurry λ n now-x≲s[n] →

                  now x                             ⊑⟨ now-x≲s→now-x⊑s n now-x≲s[n] ⟩
                  s [ n ]                           ⊑⟨ upper-bound s n ⟩■
                  ⨆ s                               ■) ⟩□

                now x ⊑ ⨆ s                    □
       ; pp = λ _ → Π-closure ext 1 λ _ →
                    ⊑-propositional
       })
    y

  from-args : Rec-args-Prop (λ x → ∀ y → x ≲ y → x ⊑ y)
  from-args = record
    { pe = λ y _ → never⊑ y
    ; po = now-lemma
    ; pl = λ s s≲→s⊑ y →
             (∀ n → s [ n ] ≲ y)  ↝⟨ (λ s[_]≲y n → s≲→s⊑ n y s[ n ]≲y) ⟩
             (∀ n → s [ n ] ⊑ y)  ↝⟨ least-upper-bound s y ⟩□
             ⨆ s ⊑ y              □
    ; pp = λ _ → Π-closure ext 1 λ _ →
                 Π-closure ext 1 λ _ →
                 ⊑-propositional
    }

------------------------------------------------------------------------
-- Some properties that follow from the equivalence between _⊑_ and
-- _≲_

-- Defined values of the form now x are never smaller than or equal
-- to never (assuming univalence).
--
-- This lemma was proved together with Paolo Capriotti and Nicolai
-- Kraus.

now⋢never : (x : A) → ¬ now x ⊑ never
now⋢never x =
  now x ⊑ never  ↔⟨ ⊑≃≲ ⟩
  now x ≲ never  ↝⟨ ⊥-elim ⟩□
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
  now x ⊑ now y  ↝⟨ ⊑≃≲ ⟩
  now x ≲ now y  ↝⟨ F.id ⟩□
  ∥ x ≡ y ∥      □

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

-- A computation can terminate with at most one value.

termination-value-merely-unique :
  ∀ {x y z} → x ⇓ y → x ⇓ z → ∥ y ≡ z ∥
termination-value-merely-unique {x} {y} {z} x⇓y x⇓z =
  _≃_.to now≡now≃∥≡∥ (
    now y  ≡⟨ sym x⇓y ⟩
    x      ≡⟨ x⇓z ⟩∎
    now z  ∎)

-- If a computation terminates with a certain value, then all larger
-- computations terminate with the same value.
--
-- Capretta proved a similar result in "General Recursion via
-- Coinductive Types".

larger-terminate-with-same-value : {x y : A ⊥} → x ⊑ y → x ≼ y
larger-terminate-with-same-value = ⊑-rec-⊑
  {Q = λ {x y} _ → x ≼ y}
  (record
     { qr = λ x z →
              x ⇓ z  ↝⟨ id ⟩□
              x ⇓ z  □
     ; qe = λ x z →
              never ⇓ z  ↝⟨ now≢never z ∘ sym ⟩
              ⊥₀         ↝⟨ ⊥-elim ⟩□
              x ⇓ z      □
     ; qu = λ s ub _ n q qu x s[n]⇓x →                 $⟨ (λ _ n≤m → lemma s (flip q x) n≤m s[n]⇓x) ⟩
              (∀ m → n ≤ m → s [ m ] ≡ now x)          ↝⟨ (λ hyp m n≤m → proj₁ (_≃_.from equality-characterisation-⊥ (hyp m n≤m))) ⟩
              (∀ m → n ≤ m → s [ m ] ⊑ now x)          ↝⟨ (λ hyp m → [ (λ m≤n →

                s [ m ]                                     ⊑⟨ later-larger s m≤n ⟩
                s [ n ]                                     ⊑⟨ s[n]⇓x ⟩≡
                now x                                       ■) , hyp m ]) ⟩

              (∀ m → m ≤ n ⊎ n ≤ m → s [ m ] ⊑ now x)  ↝⟨ (λ hyp m → hyp m (Nat.total m n)) ⟩
              (∀ m → s [ m ] ⊑ now x)                  ↝⟨ least-upper-bound s (now x) ⟩
              ⨆ s ⊑ now x                              ↝⟨ flip antisymmetry (

                now x                                       ⊑⟨ sym s[n]⇓x ⟩≡
                s [ n ]                                     ⊑⟨ upper-bound s n ⟩■
                ⨆ s                                         ■) ⟩

              ⨆ s ⇓ x                                  ↝⟨ qu x ⟩□
              ub ⇓ x                                   □
     ; ql = λ s ub _ q qu x →
         ⨆ s ⇓ x                                                  ↔⟨ inverse equality-characterisation-⊥ ⟩
         ⨆ s ⊑ now x × ⨆ s ⊒ now x                                ↔⟨ ⊑≃≲ ×-cong ⊑≃≲ ⟩
         ⨆ s ≲ now x × now x ≲ ⨆ s                                ↝⟨ id ⟩
         (∀ n → s [ n ] ≲ now x) × ∥ ∃ (λ n → now x ≲ s [ n ]) ∥  ↝⟨ (uncurry λ all → ∥∥-map (Σ-map id (λ {n} →

           now x ≲ s [ n ]                                             ↝⟨ (λ now-x≲s[n] → now-x≲s[n] , all n) ⟩
           now x ≲ s [ n ] × s [ n ] ≲ now x                           ↔⟨ inverse (⊑≃≲ ×-cong ⊑≃≲) ⟩
           now x ⊑ s [ n ] × s [ n ] ⊑ now x                           ↔⟨ equality-characterisation-⊥ ⟩
           now x ≡ s [ n ]                                             ↝⟨ sym ⟩□
           s [ n ] ⇓ x                                                 □))) ⟩

         ∥ ∃ (λ n → s [ n ] ⇓ x) ∥                                ↝⟨ Trunc.rec (⊥-is-set _ _) (uncurry (flip qu x)) ⟩□
         ub ⇓ x                                                   □
     ; qp = λ _ → ≼-propositional
     })
  where
  lemma : ∀ s {x} →
          (∀ n → s [ n ] ⇓ x → s [ suc n ] ⇓ x) →
          ∀ {m n} → m ≤ n → s [ m ] ⇓ x → s [ n ] ⇓ x
  lemma s     hyp     ≤-refl             = id
  lemma s {x} hyp {m} (≤-step {n = n} p) =
    s [ m ]     ⇓ x  ↝⟨ lemma s hyp p ⟩
    s [ n ]     ⇓ x  ↝⟨ hyp n ⟩□
    s [ suc n ] ⇓ x  □

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
≼→⊑ {x} {y} = ⊥-rec-Prop
  {P = λ x → x ≼ y → x ⊑ y}
  (record
     { pe = never ≼ y  ↝⟨ (λ _ → never⊑ y) ⟩
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

infix 4 _⇊_

_⇊_ : A ⊥ → A → Set a
x ⇊ y = now y ≲ x

-- The relations _⇓_ and _⇊_ are pointwise equivalent.

⇓≃⇊ : ∀ {x y} → (x ⇓ y) ≃ (x ⇊ y)
⇓≃⇊ {x} {y} =
  x ⇓ y      ↝⟨ ⇓≃now⊑ ⟩
  now y ⊑ x  ↝⟨ ⊑≃≲ ⟩
  now y ≲ x  ↝⟨ F.id ⟩□
  x ⇊ y      □