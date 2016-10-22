------------------------------------------------------------------------
-- The partiality monad's monad instance
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Partiality-monad.Inductive.Monad where

open import Equality.Propositional
open import H-level.Truncation.Propositional as Trunc
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
import Monad
open import Prelude hiding (⊥)

open import Bijection equality-with-J using (_↔_)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Nat equality-with-J as Nat
open import Univalence-axiom equality-with-J

open import Partiality-monad.Inductive
import Partiality-monad.Inductive.Alternative-order as Alternative-order
open import Partiality-monad.Inductive.Eliminators
open import Partiality-monad.Inductive.Monotone
open import Partiality-monad.Inductive.Omega-continuous
open import Partiality-monad.Inductive.Properties

------------------------------------------------------------------------
-- The monad instance

-- Functions of type A → B ⊥ can be lifted to /ω-continuous/ functions
-- from A ⊥ to B ⊥.

private

  =<<-args : ∀ {a b} {A : Set a} {B : Set b}
             (f : A → B ⊥) → Arguments-nd b b A
  =<<-args {B = B} f = record
    { P  = B ⊥
    ; Q  = _⊑_
    ; pe = never
    ; po = f
    ; pl = λ _ → ⨆
    ; pa = λ _ _ → antisymmetry
    ; ps = ⊥-is-set
    ; qr = λ _ → ⊑-refl
    ; qt = λ _ _ _ _ _ → ⊑-trans
    ; qe = λ _ → never⊑
    ; qu = λ _ → upper-bound
    ; ql = λ _ _ _ → least-upper-bound
    ; qp = λ _ _ → ⊑-propositional
    }

infix 50 _∗ _∗-inc_

_∗ : ∀ {a b} {A : Set a} {B : Set b} →
     (A → B ⊥) → [ A ⊥→ B ⊥]
f ∗ =
    (⊥-rec-nd (=<<-args f) , ⊑-rec-nd (=<<-args f))
  , λ s →
      ⊥-rec-nd (=<<-args f) (⨆ s)    ≡⟨ ⊥-rec-nd-⨆ (=<<-args f) s ⟩∎
      ⨆ (inc-rec-nd (=<<-args f) s)  ∎

_∗-inc_ : ∀ {a b} {A : Set a} {B : Set b} →
          (A → B ⊥) → Increasing-sequence A → Increasing-sequence B
_∗-inc_ f = inc-rec-nd (=<<-args f)

-- A universe-polymorphic variant of bind.

infixl 5 _>>=′_

_>>=′_ : ∀ {a b} {A : Set a} {B : Set b} →
         A ⊥ → (A → B ⊥) → B ⊥
x >>=′ f = proj₁ (proj₁ (f ∗)) x

-- "Computation" rules.

never->>= : ∀ {a b} {A : Set a} {B : Set b} {f : A → B ⊥} →
            never >>=′ f ≡ never
never->>= = ⊥-rec-nd-never (=<<-args _)

now->>= : ∀ {a b} {A : Set a} {B : Set b} {f : A → B ⊥} {x} →
          now x >>=′ f ≡ f x
now->>= = ⊥-rec-nd-now (=<<-args _) _

⨆->>= : ∀ {a b} {A : Set a} {B : Set b} {f : A → B ⊥} {s} →
        ⨆ s >>=′ f ≡ ⨆ (f ∗-inc s)
⨆->>= = ⊥-rec-nd-⨆ (=<<-args _) _

-- Bind is monotone.

infixl 5 _>>=-mono_

_>>=-mono_ :
  ∀ {a b} {A : Set a} {B : Set b} {x y : A ⊥} {f g : A → B ⊥} →
  x ⊑ y → (∀ z → f z ⊑ g z) → x >>=′ f ⊑ y >>=′ g
_>>=-mono_ {x = x} {y} {f} {g} x⊑y f⊑g =
  x >>=′ f ⊑⟨ proj₂ (proj₁ (f ∗)) x⊑y ⟩
  y >>=′ f ⊑⟨ ⊥-rec-⊥ (record
                { P  = λ y → y >>=′ f ⊑ y >>=′ g
                ; pe = never >>=′ f  ⊑⟨ never->>= ⟩≡
                       never         ⊑⟨ never⊑ _ ⟩■
                       never >>=′ g  ■
                ; po = λ x →
                         now x >>=′ f  ⊑⟨ now->>= ⟩≡
                         f x           ⊑⟨ f⊑g x ⟩
                         g x           ⊑⟨ sym now->>= ⟩≡
                         now x >>=′ g  ■
                ; pl = λ s ih →
                         ⨆ s >>=′ f     ⊑⟨ ⨆->>= ⟩≡
                         ⨆ (f ∗-inc s)  ⊑⟨ ⨆-mono ih ⟩
                         ⨆ (g ∗-inc s)  ⊑⟨ sym ⨆->>= ⟩≡
                         ⨆ s >>=′ g     ■
                ; pp = λ _ → ⊑-propositional
                })
                y ⟩
  y >>=′ g ■

-- Instances of the monad laws with extra universe polymorphism.

module Monad-laws where

  left-identity : ∀ {a b} {A : Set a} {B : Set b} x (f : A → B ⊥) →
                  now x >>=′ f ≡ f x
  left-identity _ _ = now->>=

  right-identity : ∀ {a} {A : Set a} (x : A ⊥) →
                   x >>=′ now ≡ x
  right-identity = ⊥-rec-⊥
    (record
       { pe = never >>=′ now  ≡⟨ never->>= ⟩∎
              never           ∎
       ; po = λ x →
                now x >>=′ now  ≡⟨ now->>= ⟩∎
                now x           ∎
       ; pl = λ s hyp →
                ⨆ s >>=′ now        ≡⟨ ⨆->>= ⟩
                ⨆ (now ∗-inc s)     ≡⟨ cong ⨆ (_↔_.to equality-characterisation-increasing λ n →

                  s [ n ] >>=′ now       ≡⟨ hyp n ⟩∎
                  s [ n ]                ∎) ⟩∎

                ⨆ s                 ∎
       ; pp = λ _ → ⊥-is-set _ _
       })

  associativity : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
                  (x : A ⊥) (f : A → B ⊥) (g : B → C ⊥) →
                  x >>=′ (λ x → f x >>=′ g) ≡ x >>=′ f >>=′ g
  associativity x f g = ⊥-rec-⊥
    (record
       { pe = (never >>=′ λ x → f x >>=′ g)  ≡⟨ never->>= ⟩
              never                          ≡⟨ sym never->>= ⟩
              never >>=′ g                   ≡⟨ cong (_>>=′ g) $ sym never->>= ⟩∎
              never >>=′ f >>=′ g            ∎
       ; po = λ x →
                (now x >>=′ λ x → f x >>=′ g)  ≡⟨ now->>= ⟩
                f x >>=′ g                     ≡⟨ cong (_>>=′ g) $ sym now->>= ⟩∎
                now x >>=′ f >>=′ g            ∎
       ; pl = λ s hyp →
                (⨆ s >>=′ λ x → f x >>=′ g)        ≡⟨ ⨆->>= ⟩
                ⨆ ((λ x → f x >>=′ g) ∗-inc s)     ≡⟨ cong ⨆ (_↔_.to equality-characterisation-increasing λ n →

                  s [ n ] >>=′ (λ x → f x >>=′ g)       ≡⟨ hyp n ⟩∎
                  s [ n ] >>=′ f >>=′ g                 ∎) ⟩

                ⨆ (g ∗-inc (f ∗-inc s))            ≡⟨ sym ⨆->>= ⟩
                ⨆ (f ∗-inc s) >>=′ g               ≡⟨ cong (_>>=′ g) (sym ⨆->>=) ⟩∎
                ⨆ s >>=′ f >>=′ g                  ∎
       ; pp = λ _ → ⊥-is-set _ _
       })
    x

open Monad equality-with-J hiding (map; map-id; map-∘)

instance

  -- The partiality monad's monad instance.

  partiality-monad : ∀ {ℓ} → Monad (_⊥ {a = ℓ})
  Raw-monad.return (Monad.raw-monad partiality-monad) = now
  Raw-monad._>>=_  (Monad.raw-monad partiality-monad) = _>>=′_
  Monad.left-identity  partiality-monad = Monad-laws.left-identity
  Monad.right-identity partiality-monad = Monad-laws.right-identity
  Monad.associativity  partiality-monad = Monad-laws.associativity

------------------------------------------------------------------------
-- _⊥ is a functor

map : ∀ {a b} {A : Set a} {B : Set b} →
      (A → B) → [ A ⊥→ B ⊥]
map f = (return ∘ f) ∗

map-id : ∀ {a} {A : Set a} →
         map (id {A = A}) ≡ idω
map-id =
  return ∗  ≡⟨ _↔_.to equality-characterisation-continuous (λ x →

    x >>= return  ≡⟨ right-identity x ⟩∎
    x             ∎) ⟩∎

  idω       ∎

map-∘ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
        (f : B → C) (g : A → B) →
        map (f ∘ g) ≡ map f ∘ω map g
map-∘ f g =
  (now ∘ f ∘ g) ∗                ≡⟨ _↔_.to equality-characterisation-continuous (λ x →

    x >>=′ (now ∘ f ∘ g)                     ≡⟨ cong (x >>=′_) (ext λ _ → sym now->>=) ⟩
    x >>=′ (λ x → now (g x) >>=′ (now ∘ f))  ≡⟨ Monad-laws.associativity x (now ∘ g) (now ∘ f) ⟩∎
    x >>=′ (now ∘ g) >>=′ (now ∘ f)          ∎) ⟩∎

  (now ∘ f) ∗ ∘ω (now ∘ g) ∗  ∎

------------------------------------------------------------------------
-- Some properties

-- A kind of inversion lemma for _⇓_.

>>=-⇓ :
  ∀ {a b} {A : Set a} {B : Set b}
    {x : A ⊥} {f : A → B ⊥} {y} →
  Univalence a →
  Univalence b →
  (x >>=′ f ⇓ y) ≃ ∥ ∃ (λ z → x ⇓ z × f z ⇓ y) ∥
>>=-⇓ {x = x} {f} {y} univ-a univ-b = ⊥-rec-⊥
  (record
     { P  = λ x → (x >>=′ f ⇓ y) ≃ ∥ ∃ (λ z → x ⇓ z × f z ⇓ y) ∥
     ; pe = never >>=′ f ⇓ y                         ↔⟨ ≡⇒↝ bijection (cong (_⇓ y) never->>=) ⟩
            never ⇓ y                                ↝⟨ B.⇓≃now≲ ⟩
            now y B.≲ never                          ↔⟨ ≡⇒↝ bijection B.now≲never ⟩
            Prelude.⊥                                ↔⟨ inverse (not-inhabited⇒∥∥↔⊥ id) ⟩
            ∥ Prelude.⊥ ∥                            ↔⟨ ∥∥-cong (inverse ×-right-zero) ⟩
            ∥ ∃ (λ z → ⊥₀) ∥                         ↔⟨ ∥∥-cong (∃-cong (λ _ → inverse ×-left-zero)) ⟩
            ∥ ∃ (λ z → Prelude.⊥       × f z ⇓ y) ∥  ↝⟨ ∥∥-cong (∃-cong (λ _ → ≡⇒↝ _ (sym A.now≲never) ×-cong F.id)) ⟩
            ∥ ∃ (λ z → now z A.≲ never × f z ⇓ y) ∥  ↔⟨ ∥∥-cong (∃-cong (λ _ → inverse (Alternative-order.⇓≃now≲ univ-a) ×-cong F.id)) ⟩□
            ∥ ∃ (λ z → never ⇓ z       × f z ⇓ y) ∥  □
     ; po = λ x →
              now x >>=′ f ⇓ y                                   ↔⟨ ≡⇒↝ bijection (cong (_⇓ y) now->>=) ⟩
              f x ⇓ y                                            ↔⟨ inverse (∥∥↔ (⊥-is-set _ _)) ⟩
              ∥ f x ⇓ y ∥                                        ↔⟨ ∥∥-cong (inverse $ drop-⊤-left-Σ $ inverse $
                                                                      _⇔_.to contractible⇔⊤↔ (singleton-contractible _)) ⟩
              ∥ ∃ (λ (p : ∃ (λ z → z ≡ x)) → f (proj₁ p) ⇓ y) ∥  ↔⟨ ∥∥-cong (inverse Σ-assoc) ⟩
              ∥ ∃ (λ z → z ≡ x × f z ⇓ y) ∥                      ↔⟨ inverse $ Trunc.flatten′
                                                                      (λ F → ∃ (λ _ → F (_ ≡ _) × _))
                                                                      (λ f → Σ-map id (Σ-map f id))
                                                                      (λ { (x , y , z) → ∥∥-map ((x ,_) ∘ (_, z)) y }) ⟩
              ∥ ∃ (λ z → ∥ z ≡ x ∥       × f z ⇓ y) ∥            ↝⟨ ∥∥-cong (∃-cong λ _ → ≡⇒↝ _ (sym A.now≲now) ×-cong F.id) ⟩
              ∥ ∃ (λ z → now z A.≲ now x × f z ⇓ y) ∥            ↝⟨ ∥∥-cong (∃-cong λ _ → inverse A.⇓≃now≲ ×-cong F.id) ⟩□
              ∥ ∃ (λ z → now x ⇓ z       × f z ⇓ y) ∥            □
     ; pl = λ s ih →
              ⨆ s >>=′ f ⇓ y                                     ↔⟨ ≡⇒↝ bijection (cong (_⇓ y) ⨆->>=) ⟩
              ⨆ (f ∗-inc s) ⇓ y                                  ↝⟨ B.⨆⇓≃∥∃⇓∥ _ ⟩
              ∥ (∃ λ n → s [ n ] >>=′ f ⇓ y) ∥                   ↝⟨ ∥∥-cong (∃-cong ih) ⟩
              ∥ (∃ λ n → ∥ ∃ (λ z → s [ n ] ⇓ z × f z ⇓ y) ∥) ∥  ↔⟨ Trunc.flatten′ (λ F → ∃ λ _ → F (∃ λ _ → _ × _))
                                                                                   (λ f → Σ-map id f)
                                                                                   (uncurry λ x → ∥∥-map (x ,_)) ⟩
              ∥ (∃ λ n → ∃ λ z → s [ n ] ⇓ z × f z ⇓ y) ∥        ↔⟨ ∥∥-cong ∃-comm ⟩
              ∥ (∃ λ z → ∃ λ n → s [ n ] ⇓ z × f z ⇓ y) ∥        ↔⟨ ∥∥-cong (∃-cong λ _ → Σ-assoc) ⟩
              ∥ (∃ λ z → (∃ λ n → s [ n ] ⇓ z) × f z ⇓ y) ∥      ↔⟨ inverse $ Trunc.flatten′
                                                                      (λ F → (∃ λ _ → F (∃ λ _ → _ ⇓ _) × _))
                                                                      (λ f → Σ-map id (Σ-map f id))
                                                                      (λ { (x , y , z) → ∥∥-map ((x ,_) ∘ (_, z)) y }) ⟩
              ∥ (∃ λ z → ∥ (∃ λ n → s [ n ] ⇓ z) ∥ × f z ⇓ y) ∥  ↝⟨ ∥∥-cong (∃-cong λ _ → inverse (A.⨆⇓≃∥∃⇓∥ _) ×-cong F.id) ⟩□
              ∥ ∃ (λ z → ⨆ s ⇓ z × f z ⇓ y) ∥                    □
     ; pp = λ _ → Eq.right-closure ext 0 truncation-is-proposition
     })
  x
  where
  module A = Alternative-order univ-a
  module B = Alternative-order univ-b

-- □ is closed, in a certain sense, under bind (assuming univalence).

□->>= :
  ∀ {a b p q} {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q}
    {x : A ⊥} {f : A → B ⊥} →
  Univalence a →
  Univalence b →
  (∀ x → Is-proposition (Q x)) →
  □ P x → (∀ {x} → P x → □ Q (f x)) → □ Q (x >>=′ f)
□->>= {Q = Q} {x} {f} univ-a univ-b Q-prop □-x □-f y =
  x >>=′ f ⇓ y                   ↔⟨ >>=-⇓ univ-a univ-b ⟩
  ∥ (∃ λ z → x ⇓ z × f z ⇓ y) ∥  ↝⟨ Trunc.rec (Q-prop y) (λ { (z , x⇓z , fz⇓y) → □-f (□-x z x⇓z) y fz⇓y }) ⟩□
  Q y                            □

-- ◇ is closed, in a certain sense, under bind.

◇->>= :
  ∀ {a b p q} {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q}
    {x : A ⊥} {f : A → B ⊥} →
  ◇ P x → (∀ {x} → P x → ◇ Q (f x)) → ◇ Q (x >>=′ f)
◇->>= {x = x} {f} ◇-x ◇-f = Trunc.rec
  truncation-is-proposition
  (λ { (y , x⇓y , Py) →
       ∥∥-map (λ { (z , fy⇓z , Qz) →
                     z
                   , (x >>=′ f      ≡⟨ cong (_>>=′ f) x⇓y ⟩
                      now y >>=′ f  ≡⟨ now->>= ⟩
                      f y           ≡⟨ fy⇓z ⟩∎
                      now z         ∎)
                   , Qz
                 })
              (◇-f Py)
     })
  ◇-x

-- Certain nested occurrences of ⨆ can be replaced by a single one
-- (assuming univalence).

⨆>>=⨆≡⨆>>= :
  ∀ {a b} {A : Set a} {B : Set b} →
  Univalence a →
  Univalence b →
  ∀ (s : Increasing-sequence A) (f : A → Increasing-sequence B)
    {inc₁ inc₂} →
  ⨆ ((λ n → s [ n ] >>=′ ⨆ ∘ f) , inc₁) ≡
  ⨆ ((λ n → s [ n ] >>=′ λ y → f y [ n ]) , inc₂)
⨆>>=⨆≡⨆>>= univ-a univ-b s f = antisymmetry
  (least-upper-bound _ _ λ n →
   _≃_.to (Alternative-order.≼≃⊑ univ-b) $ λ z →

     s [ n ] >>=′ ⨆ ∘ f ⇓ z                                   ↔⟨ >>=-⇓ univ-a univ-b ⟩
     ∥ (∃ λ y → s [ n ] ⇓ y × ⨆ (f y) ⇓ z) ∥                  ↔⟨ ∥∥-cong (∃-cong λ _ → F.id ×-cong Alternative-order.⨆⇓≃∥∃⇓∥ univ-b _) ⟩
     ∥ (∃ λ y → s [ n ] ⇓ y × ∥ (∃ λ m → f y [ m ] ⇓ z) ∥) ∥  ↔⟨ Trunc.flatten′
                                                                   (λ F → ∃ λ _ → _ × F (∃ λ _ → _ ⇓ _))
                                                                   (λ f → Σ-map id (Σ-map id f))
                                                                   (λ { (y , p , q) → ∥∥-map ((y ,_) ∘ (p ,_)) q }) ⟩
     ∥ (∃ λ y → s [ n ] ⇓ y × ∃ λ m → f y [ m ] ⇓ z) ∥        ↔⟨ ∥∥-cong (∃-cong λ _ → ∃-comm) ⟩
     ∥ (∃ λ y → ∃ λ m → s [ n ] ⇓ y × f y [ m ] ⇓ z) ∥        ↝⟨ ∥∥-map (Σ-map id lemma) ⟩
     ∥ (∃ λ y → ∃ λ m → s [ m ] ⇓ y × f y [ m ] ⇓ z) ∥        ↔⟨ ∥∥-cong ∃-comm ⟩
     ∥ (∃ λ m → ∃ λ y → s [ m ] ⇓ y × f y [ m ] ⇓ z) ∥        ↔⟨ inverse $ Trunc.flatten′
                                                                   (λ F → ∃ λ _ → F (∃ λ _ → _ × _))
                                                                   (λ f → Σ-map id f)
                                                                   (λ { (m , p) → ∥∥-map (m ,_) p }) ⟩
     ∥ (∃ λ m → ∥ (∃ λ y → s [ m ] ⇓ y × f y [ m ] ⇓ z) ∥) ∥  ↔⟨ ∥∥-cong (∃-cong λ _ → inverse $ >>=-⇓ univ-a univ-b) ⟩
     ∥ (∃ λ m → (s [ m ] >>=′ λ y → f y [ m ]) ⇓ z) ∥         ↔⟨ inverse $ Alternative-order.⨆⇓≃∥∃⇓∥ univ-b _ ⟩□
     ⨆ ((λ m → s [ m ] >>=′ λ y → f y [ m ]) , _) ⇓ z         □)

  (⨆-mono λ n →

    (s [ n ] >>=′ λ y → f y [ n ])  ⊑⟨ ⊑-refl (s [ n ]) >>=-mono (λ y → upper-bound (f y) n) ⟩■
    (s [ n ] >>=′ ⨆ ∘ f)            ■)

  where
  lemma :
    ∀ {n y z} →
    (∃ λ m → s [ n ] ⇓ y × f y [ m ] ⇓ z) →
    (∃ λ m → s [ m ] ⇓ y × f y [ m ] ⇓ z)
  lemma {n} (m , p , q) with Nat.total m n
  ... | inj₁ m≤n = n
                 , p
                 , _≃_.from (Alternative-order.≼≃⊑ univ-b)
                     (later-larger (f _) m≤n) _ q
  ... | inj₂ n≤m = m
                 , _≃_.from (Alternative-order.≼≃⊑ univ-a)
                     (later-larger s n≤m) _ p
                 , q
