
-- Goal of this module: establish an equivalence between
-- the QIIT partiality monad and the quotiented delay monad
-- (assuming countable choice, and funext).

{-# OPTIONS --without-K #-}

module Countchoice-equiv where

open import Prelude
open import Equality
open import Equality.Propositional hiding (elim)
open import H-level equality-with-J -- hiding (Surjective)
open import H-level.Closure equality-with-J
open import Logical-equivalence hiding (_∘_)
open import Nat equality-with-J
open import Equivalence equality-with-J hiding (_∘_)

open import Quotient.HIT hiding ([_])

-- open import H-level.Truncation equality-with-J hiding (rec)

open import H-level.Truncation.Propositional hiding (rec)


-- We assume function extensionality without restriction.
-- I don't think we would be able to do much without.
postulate
  ext : ∀ {a b} → Extensionality a b


-- Here are some library lemmas. I include them here in ad-hoc style (should be sorted out later).
module library-stuff where

  module _ {a} {A : Set a} where

    disj-constructors : {a : A} → nothing ≢ just a
    disj-constructors () 

    just-injective : {b c : A} → _≡_ {A = Maybe A} (just b) (just c) → b ≡ c
    just-injective refl = refl

  lib-lemma : {m n : ℕ} → (m ≤ n) → (n ≤ m) → m ≡ n
  lib-lemma = {!!}

  -- small improvement of ≰→≥
  m≰n→Sn≤m : {m n : ℕ} → ¬(m ≤ n) → suc n ≤ m
  m≰n→Sn≤m = {!!}

  suc≤suc→≤ : {m n : ℕ} → suc m ≤ suc n → m ≤ n
  suc≤suc→≤ = {!!}

  ≤-is-prop : {m n : ℕ} → Is-proposition (m ≤ n)
  ≤-is-prop = {!!}

  -- if P is a property of A (i.e. a family of propositions over A),
  -- then it is enough to show that any two elements of a which satisfy P
  -- in order to conclude that Σ A P is propositional.
  Σ-property : ∀ {α} {β} (A : Set α) (P : A → Set β) → ((a : A) → Is-proposition (P a)) → ((x y : Σ A P) → proj₁ x ≡ proj₁ y) → Is-proposition (Σ A P)
  Σ-property = {!!}

  
open library-stuff

-- my version of monotone sequences. 
module monotone-sequences {a} {Aset : SET a} where

  A = proj₁ Aset
  A-is-set = proj₂ Aset

  -- works only because A is a set, of course.
  MA-is-set : Is-set (Maybe A)
  MA-is-set = ⊎-closure 0 (mono₁ 1 (mono₁ 0 ⊤-contractible)) A-is-set

  -- a predicate stating that a function ℕ → Maybe A is monotone
  is-monotone : (f : ℕ → Maybe A) → Set a
  is-monotone f = (n : ℕ) → (f n ≡ f (suc n)) ⊎ f n ≡ nothing × f (suc n) ≢ nothing


  {- this part only works because of the assumption that A is a set.
     The equivalence with Delay A should work more generally (todo: check this claim),
     but it's probably not worth it to emphasize this anyway: As soon as we go to
     A ⊥, we can only work with sets (otherwise, we would have to change the QIIT to a
     HIIT with infinite coherences). -}
  -- surely, there is a more elegant way to do this?!
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

  -- equality on Seq
  Seq≡ : (s₁ s₂ : Seq) → ((n : ℕ) → proj₁ s₁ n ≡ proj₁ s₂ n) → s₁ ≡ s₂
  Seq≡ (f , _) (g , _) p = Σ-≡,≡→≡ (ext p) (_⇔_.to propositional⇔irrelevant (is-monotone-is-prop _) _ _) 

  -- shift and unshift: operations of sequences that add or remove an element in the beginning.
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


  -- What now follows is a bunch of straightforward boring lemmas.

  seq-stable-step : (fp : Seq) (m : ℕ) → (a : A) → (proj₁ fp m ≡ just a) → proj₁ fp (suc m) ≡ just a
  seq-stable-step (f , p) m a fm≡justₐ with p m
  seq-stable-step (f , p) m a fm≡justₐ | inj₁ fm≡fSm = trans (sym fm≡fSm) fm≡justₐ
  seq-stable-step (f , p) m a fm≡justₐ | inj₂ (fm≡nothing , _) = ⊥-elim (disj-constructors (trans (sym fm≡nothing) fm≡justₐ))

  seq-stable : (fp : Seq) (m n : ℕ) → (m ≤ n) → (a : A) → (proj₁ fp m ≡ just a) → proj₁ fp n ≡ just a
  seq-stable (f , p) m n (_≤_.≤-refl′ m≡n) a q = subst (λ k → f k ≡ just a) m≡n q
  seq-stable (f , p) m n (_≤_.≤-step′ {k} m≤k Sk≡n) a q = subst (λ o → f o ≡ just a) Sk≡n (seq-stable-step (f , p) k a (seq-stable (f , p) m k m≤k a q))  

  -- if fn ≡ a and fm ≡ b, then a ≡ b. 
  seq-unique-element : (fp : Seq) (m n : ℕ) (a b : A) → (proj₁ fp m ≡ just a) × (proj₁ fp n ≡ just b) → a ≡ b
  seq-unique-element (f , p) m n a b (fm≡a , fn≡b) with total m n
  seq-unique-element (f , p) m n a b (fm≡a , fn≡b) | inj₁ m≤n = just-injective (trans (sym (seq-stable (f , p) m n m≤n a fm≡a)) fn≡b) 
  seq-unique-element (f , p) m n a b (fm≡a , fn≡b) | inj₂ n≤m = just-injective (trans (sym fm≡a) (seq-stable (f , p) n m n≤m b fn≡b))

  -- if fSn ≡ nothing, then fn ≡ nothing
  smaller-nothing-step : (fp : Seq) (n : ℕ) → proj₁ fp (suc n) ≡ nothing → proj₁ fp n ≡ nothing
  smaller-nothing-step (f , p) n fSn≡nothing with p n
  smaller-nothing-step (f , p) n fSn≡nothing | inj₁ fn≡fSn = trans fn≡fSn fSn≡nothing
  smaller-nothing-step (f , p) n fSn≡nothing | inj₂ (fn≡nothing , _) = fn≡nothing

  -- if fn ≡ nothing, then fm ≡ nothing for m ≤ n
  smaller-nothing : (fp : Seq) (m n : ℕ) → (m ≤ n) → proj₁ fp n ≡ nothing → proj₁ fp m ≡ nothing
  smaller-nothing (f , p) m n (_≤_.≤-refl′ m≡n) fn≡nothing = subst (λ k → f k ≡ nothing) (sym m≡n) fn≡nothing
  smaller-nothing (f , p) m n (_≤_.≤-step′ {k} m≤k Sk≡n) fn≡nothing =
    smaller-nothing (f , p) m k m≤k
                    (smaller-nothing-step (f , p) k (subst (λ j → f j ≡ nothing) (sym Sk≡n) fn≡nothing))

  -- if fm ≡ nothing and fn ≡ just a, then Sm ≤ n.
  nothing-just-compare : (fp : Seq) (a : A) (m n : ℕ) → (proj₁ fp m ≡ nothing) → (proj₁ fp n ≡ just a) → suc m ≤ n
  nothing-just-compare (f , p) a m n fm≡nothing fn≡justₐ with suc m ≤? n
  nothing-just-compare (f , p) a m n fm≡nothing fn≡justₐ | inj₁  Sm≤n = Sm≤n
  nothing-just-compare (f , p) a m n fm≡nothing fn≡justₐ | inj₂ ¬Sm≤n = ⊥-elim (disj-constructors (trans (sym (smaller-nothing (f , p) n m n≤m fm≡nothing)) fn≡justₐ))
    where
      Sn≤Sm : suc n ≤ suc m
      Sn≤Sm = m≰n→Sn≤m ¬Sm≤n
      n≤m : n ≤ m
      n≤m = suc≤suc→≤ Sn≤Sm


  -- I define two variants of the ↓ relation; f ↓ a says that the sequence f "evaluates" to a.
  -- The two variants are both propositional, and they are equivalent.
  -- One is defined with truncation and one without.
  -- The point is that:
  -- (*) with truncation, it is easier to *show* that a sequence 'evaluates' to a
  -- (*) without truncation, it is easier to *use* the fact that a sequence 'evaluates' to a.

  _↓_ : Seq → A → Set _
  (f , m) ↓ a = Σ ℕ (λ n → f n ≡ just a × ((n' : ℕ) → (f n' ≢ nothing) → n ≤ n')) -- CAVEAT: this could possibly be nicer with <; but it's fine as it is here, I guess.

  ↓-is-prop : (fp : Seq) → (a : A) → Is-proposition (fp ↓ a)
  ↓-is-prop (f , p) a = Σ-property _ _ (λ _ → ×-closure 1 (MA-is-set _ _)
                                   (Π-closure ext 1 (λ _ → Π-closure ext 1 (λ _ → ≤-is-prop)))) number-unique
    where
      number-unique : (x y : (f , p) ↓ a) → proj₁ x ≡ proj₁ y
      number-unique (m , p₁ , p₂) (n , q₁ , q₂) = lib-lemma (p₂ n (λ e → disj-constructors (trans (sym e) q₁)))
                                                            (q₂ m (λ e → disj-constructors (trans (sym e) p₁)))

  _∥↓∥_ : Seq → A → Set _
  (f , m) ∥↓∥ a = ∥ (Σ ℕ λ n → f n ≡ just a) ∥ 

  ∥↓∥-is-prop : (fp : Seq) → (a : A) → Is-proposition (fp ∥↓∥ a)
  ∥↓∥-is-prop fp a = truncation-is-proposition

  -- now: the equivalence of ↓ and ∥↓∥
  ↓→∥↓∥ : ∀ {fp} {a} → (fp ↓ a) → (fp ∥↓∥ a)
  ↓→∥↓∥ = ?


  -- however, we can also define it with truncation. The point is that:
  -- (*) with truncation, it is easier to *show* that a sequence 'evaluates' to a
  -- (*) without truncation, it is easier to *use* the fact that a sequence 'evaluates' to a.
  -- Fortunately, they are equivalent.

  -- TODO: do this. then, delete the work done later which I had to do without this abstraction.




  -- if *any* element in a sequence is a, then the sequence 'evaluates' to a
  any≡a→↓a : (fp : Seq) → (a : A) → (n : ℕ) → (proj₁ fp n ≡ just a) → fp ↓ a
  any≡a→↓a (f , p) a zero    fn≡justₐ = zero , fn≡justₐ , (λ _ _ → zero≤ _)
  any≡a→↓a (f , p) a (suc n) fSn≡justₐ with inspect (f n)
  any≡a→↓a (f , p) a (suc n) fSn≡justₐ | nothing , fn≡nothing = suc n , fSn≡justₐ , Sn-is-min 
    where
      Sn-is-min : (n' : ℕ) → (f n' ≢ nothing) → suc n ≤ n'
      Sn-is-min n' fn'≢nothing with inspect (f n')
      Sn-is-min n' fn'≢nothing | nothing , fn'≡nothing = ⊥-elim (fn'≢nothing fn'≡nothing)
      Sn-is-min n' fn'≢nothing | just b , fn'≡justb    = nothing-just-compare (f , p) b n n' fn≡nothing fn'≡justb
  any≡a→↓a (f , p) a (suc n) fSn≡justₐ | just b , fn≡justb with any≡a→↓a (f , p) b n fn≡justb
  any≡a→↓a (f , p) a (suc n) fSn≡justₐ | just b , fn≡justb | min , (fmin≡justb , min-is-min) = min , fmin≡justa , min-is-min  where

    fmin≡justa : f min ≡ just a
    fmin≡justa = subst (λ c → f min ≡ just c) (seq-unique-element (f , p) min (suc n) b a (fmin≡justb , fSn≡justₐ)) fmin≡justb 



  {-
    _⇔_.from propositional⇔irrelevant
      (λ { x y → Σ-≡,≡→≡ (number-unique x y) {!_⇔_.to propositional⇔irrelevant ?!} }) where

        number-unique : (x y : (f , p) ↓ a) → proj₁ x ≡ proj₁ y
        number-unique (m , p₁ , p₂) (n , q₁ , q₂) = lib-lemma (p₂ n (λ e → disj-constructors (trans (sym e) q₁)))
                                                              (q₂ m (λ e → disj-constructors (trans (sym e) p₁)))
-}

  -- auxiliary relations that we will use to define the equivalence relation on sequences
  
  _≲_ : Seq → Seq → Set _
  f ≲ g = (a : A) → (f ↓ a) → (g ↓ a)

  ≲-is-prop : (f g : Seq) → Is-proposition (f ≲ g)
  ≲-is-prop f g = Π-closure ext 1 (λ a → Π-closure ext 1 (λ _ → ↓-is-prop g a))

  _~_ : Seq → Seq → Set _
  f ~ g = (f ≲ g) × (g ≲ f)

  ~-is-prop : (f g : Seq) → Is-proposition (f ~ g)
  ~-is-prop f g = ×-closure 1 (≲-is-prop f g) (≲-is-prop g f)

  -- quotiented sequences
  Seq/~ : Set _
  Seq/~ = Seq / (λ f g → (f ~ g , ~-is-prop f g))


module monotone-and-QIIT {a} {Aset : SET a} where

  open monotone-sequences {a} {Aset}

  open import Partiality-monad.Inductive 
  open import Partiality-monad.Inductive.Properties

  -- the first goal is to define the canonical function from Sequences to the QIIT-partiality monad

  aux : Maybe A → _⊥ A 
  aux nothing  = never
  aux (just a) = now a 

  mon→⊑-pointwise : (x y : Maybe A) → ((x ≡ y) ⊎ x ≡ nothing × y ≢ nothing) → aux x ⊑ aux y
  mon→⊑-pointwise x .x (inj₁ refl) = ⊑-refl _
  mon→⊑-pointwise .nothing y (inj₂ (refl , y≢n)) = never⊑ _

  Seq→Increasing : Seq → Increasing-sequence A
  Seq→Increasing (f , p) = aux ∘ f , (λ n → mon→⊑-pointwise (f n) (f (suc n)) (p n))

  canonical : Seq → (_⊥ A)
  canonical = ⨆ ∘ Seq→Increasing

  canonical-≲-⊑ : {fp gq : Seq} → fp ≲ gq → canonical fp ⊑ canonical gq
  canonical-≲-⊑ {f , p} {gq} fp≲gq =
    least-upper-bound (Seq→Increasing (f , p))
                      (canonical gq)
                      cgq-is-ub
               where

               cgq-is-ub : (n : ℕ) → Seq→Increasing (f , p) [ n ] ⊑ canonical gq
               cgq-is-ub n with inspect (f n)
               cgq-is-ub n | nothing , fn≡nothing = subst (λ x → x ⊑ _) (cong aux (sym fn≡nothing)) (never⊑ _)
               cgq-is-ub n | inj₂ a , fn≡justₐ =  aux (f n)  ⊑⟨ subst (λ maybe → aux (f n) ⊑ aux maybe) (trans fn≡justₐ (sym gkₙ≡justₐ)) (⊑-refl _) ⟩
                                                  aux (g kₙ) ⊑⟨ upper-bound′ (Seq→Increasing gq) (⨆ (Seq→Increasing gq)) (⊑-refl _) kₙ ⟩■
                                                  ⨆ (Seq→Increasing gq) ■
                 where
                 g = proj₁ gq
                 fp↓a : (f , p) ↓ a
                 fp↓a = any≡a→↓a (f , p) a n fn≡justₐ
                 gq↓a : gq ↓ a
                 gq↓a = fp≲gq a fp↓a
                 kₙ : ℕ 
                 kₙ = proj₁ gq↓a
                 gkₙ≡justₐ : g kₙ ≡ just a
                 gkₙ≡justₐ = proj₁ (proj₂ gq↓a)


  canonical-respects-~ : {fp gq : Seq} → fp ~ gq → canonical fp ≡ canonical gq
  canonical-respects-~ (fp≲gq , gq≲fp) = antisymmetry (canonical-≲-⊑ fp≲gq) (canonical-≲-⊑ gq≲fp)

  -- Finally, we can extend the canonical function to the quotient.
  canonical' : Seq/~ → (_⊥ A)
  canonical' = rec {P = _⊥ A} canonical canonical-respects-~ ⊥-is-set 

  -- ... and this is really an extension.
  canonical'-is-extension : (fp : Seq) → canonical' (Quotient.HIT.[_] fp) ≡ canonical fp
  canonical'-is-extension fp = {!refl!}

module canonical-simple-properties {a} {Aset : SET a} where

  open import Partiality-monad.Inductive 
  open import Partiality-monad.Inductive.Properties
  open monotone-sequences {a} {Aset}
  open monotone-and-QIIT {a} {Aset}

  -- sequence constantly nothing
  const-nothing : Seq
  const-nothing = (λ _ → nothing) , (λ _ → inj₁ refl)

  -- the canonical function maps the constantly nothing sequence to 'never'
  canonical-nothing-never : canonical const-nothing ≡ never
  canonical-nothing-never = antisymmetry {x = canonical const-nothing} {y = never}
                                         (least-upper-bound _ never (λ _ → ⊑-refl never))
                                         (never⊑ _)

  -- sequencs constantly just a
  const-seq : (a : A) → Seq
  const-seq  a = (λ _ → just a) , (λ _ → inj₁ refl)

  -- the canonical function maps the constantly a sequence to 'now a'
  canonical-const-now : (a : A) → canonical (const-seq a) ≡ now a
  canonical-const-now a = antisymmetry {x = canonical (const-seq a)} {y = now a}
                                       (least-upper-bound _ (now a) (λ _ → ⊑-refl _))
                                       (upper-bound′ (Seq→Increasing (const-seq a)) (canonical (const-seq a)) (⊑-refl _) zero)



{-
surjective : ∀ {a} {b} {A : Set a} {B : Set b} → (f : A → B) → Set _
surjective {A = A} {B = B} f = (b : B) → {!!}

surjective : ∀ {a} {b} {A : Set a} {B : Set b} → (f : A → B) → Set _
surjective f = {!Surjective!}
-}

-- This is "countable choice".
{-
countchoice : ∀ {α} {β} → Set _
countchoice {α} {β} = (B : ℕ → Set α) → ((n : ℕ) → ∥ (B n) ∥ 1 β) → ∥ ((n : ℕ) → B n) ∥ 1 β 
-}
-- I had overlooked that this is already defined in Propositional.agda.

-- The goal of the following module is to show that the canonical function
-- (and thus the extended version of it) is surjective.

module canonical-surjective {a} {Aset : SET a} where

  open import Partiality-monad.Inductive.Eliminators

  -- contains axiom of countable choice 
--  open import H-level.Truncation.Propositional

  open monotone-and-QIIT {a} {Aset} 
  open monotone-sequences {a} {Aset}
  open canonical-simple-properties {a} {Aset}

  canonical-surjective : (Axiom-of-countable-choice a) → Surjective canonical
  canonical-surjective cc =
    ⊥-rec-⊥ {P = λ x → ∥ (Σ Seq λ fp → canonical fp ≡ x) ∥}
      (record { pe = ∣ const-nothing , canonical-nothing-never ∣ ;
                po = λ a → ∣ const-seq a , canonical-const-now a ∣ ;
                pl = λ {(f⊥ , f⊥-inc) pointwise → {!cc _ pointwise!}} ;
                pp = λ _ → truncation-is-proposition })

  -- now: canonical'-surjective

-- canonical' is injective
module canonical'-injective {a} {Aset : SET a} where


-- canonical' is an equivalence: needs a library lemma which (I think) is not there yet.
module canonical'-equivalence {a} {Aset : SET a} where




-- coinductive Delay and monotone sequences
-- this part is a desaster at the moment. Please stop reading.
module delay-and-monotone {a} {Aset : SET a} where

  open import Delay-monad
  open monotone-sequences {a} {Aset}

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
  D→Seq-lem y = Seq≡ _ _ (D→Seq-lem-aux _) where
    D→Seq-lem-aux : (y : _) → (n : ℕ) → proj₁ (D→Seq (later y)) n ≡ proj₁ (shift (D→Seq (force y))) n
    D→Seq-lem-aux y zero = refl
    D→Seq-lem-aux y (suc n) = refl



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

  -- another lemma
  Seq→D-lem : (fm : _) → {! (later (Seq→D fm))!}  ≡ Seq→D (shift fm)
  Seq→D-lem fm = {! (Seq→D fm)!}

  test : (x : ∞Delay A ∞) → (y : Delay A ∞) → ℕ
  test x y = {!later  (x)!}


  D→Set→D : (x : Delay A ∞) → Seq→D (D→Seq x) ≡ x
  D→Set→D (now a)   = refl
  D→Set→D (later y) =
    Seq→D (D→Seq (later y))
      ≡⟨ cong Seq→D (D→Seq-lem _) ⟩
    Seq→D (shift (D→Seq (force y)))
{-      ≡⟨ {!!} ⟩
    {!  ( (Seq→D (unshift (shift (D→Seq (force y))))))!}
      ≡⟨ {!!} ⟩ 

    {!later (force (Seq→D (unshift (shift (D→Seq (force y))))))!}
      ≡⟨ {!!} ⟩
    {!!}  -}
      ≡⟨ {!!} ⟩ 
    later y ∎ 



  Delay≃Seq : Delay A ∞ ≃ Seq -- (Delay A) ≃  Seq
  Delay≃Seq = ↔⇒≃ (record { surjection = record { logical-equivalence = record { to = {!!} ; from = {!!} } ; right-inverse-of = λ x → {!!} } ; left-inverse-of = λ x → {!!} })
