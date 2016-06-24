{-
  TODO:
  1. fix the module structure
  2. avoid nested 'where's
  3. fill in the gaps, obviously
  4. look at other TODOs below
-}


-- Goal of this module: establish an equivalence between
-- the QIIT partiality monad and the quotiented delay monad
-- (assuming countable choice, and funext).

{-# OPTIONS --without-K #-}

open import Equality.Propositional hiding (elim)
open import Univalence-axiom equality-with-J

module Countchoice-equiv {a} (ua : Univalence a) where

open import Prelude hiding (⊥)
open import Equality
open import H-level equality-with-J 
open import H-level.Closure equality-with-J
open import Logical-equivalence hiding (_∘_)
open import Nat equality-with-J
open import Equivalence equality-with-J hiding (_∘_)

open import Quotient.HIT hiding ([_])
open import H-level.Truncation.Propositional renaming (rec to ∥∥-rec)

open import Interval using (ext)

open import Equality.Decision-procedures equality-with-J

-- Here are some library lemmas. I include them here in ad-hoc style (should be sorted out later).
module library-stuff where

  open import Function-universe equality-with-J

  -- If X -> Y is injective + surjective, and if Y is a set, then f is an equivalence.
  module _ {α β} {X : Set α} {Yset : SET β} where

    open import Bijection equality-with-J
    open import Injection equality-with-J
    open import Surjection equality-with-J
    open import Preimage equality-with-J
    open import H-level.Closure equality-with-J

 --   open import Derived-definitions-and-properties equality-with-J

    Y = proj₁ Yset
    
    InjSurj→≃ : (f : X → Y) → (Injective f) → (Surjective f) → Is-equivalence f
    InjSurj→≃ f inj surj y = propositional⇒inhabited⇒contractible
                               (preim-is-prop y)
                               (preim-is-inh y)
      where
        preim-irrelevant : (y : Y) → (xq₁ xq₂ : f ⁻¹ y) → xq₁ ≡ xq₂
        preim-irrelevant y (x₁ , q₁) (x₂ , q₂) =
          Σ-≡,≡→≡ (inj (trans q₁ (sym q₂)))
                  (_⇔_.to propositional⇔irrelevant (proj₂ Yset _ _) _ _)
        preim-is-prop : (y : Y) → Is-proposition (f ⁻¹ y) 
        preim-is-prop y = _⇔_.from propositional⇔irrelevant (preim-irrelevant y)
        preim-is-inh : (y : Y) → f ⁻¹ y
        preim-is-inh y = _↔_.to (∥∥↔ (preim-is-prop y)) (surj y)



  -- if P is a property of A (i.e. a family of propositions over A),
  -- then it is enough to show that any two elements of a which satisfy P
  -- in order to conclude that Σ A P is propositional.
  Σ-property : ∀ {α} {β} (A : Set α) (P : A → Set β)
              → ((a : A) → Is-proposition (P a))
              → ((x y : Σ A P) → proj₁ x ≡ proj₁ y)
              → Is-proposition (Σ A P)
  Σ-property A P prop proj≡ =
    _⇔_.from propositional⇔irrelevant pairs-equal
      where
        pairs-equal : (ap₁ ap₂ : Σ A P) → ap₁ ≡ ap₂
        pairs-equal ap₁ ap₂ = Σ-≡,≡→≡ {p₁ = ap₁} {p₂ = ap₂} (proj≡ ap₁ ap₂) (_⇔_.to propositional⇔irrelevant (prop _) _ _)


  module _ {α β} {S : Set α} {R : S → S → Proposition β} where

    open import Quotient.HIT renaming (elim to /elim)

    -- An eliminator for the quotient, if the goal is propositional.
    -- This is just a simplification of the "full" eliminator.
    -- (Note: We could weaken one assumption and say that only P [ x ]
    -- is propositional.) 
    quot-elim-prop :
      ∀ {γ} → (P : S / R → Set γ) → 
      (p-[] : ∀ x → P [ x ]) →
      (∀ x → Is-proposition (P x)) →
      ∀ x → P x
    quot-elim-prop P p-[] prop
      = /elim P p-[]
              (λ _ → _⇔_.to propositional⇔irrelevant (prop [ _ ]) _ _)
              (λ x → mono₁ 1 (prop x)) 


  module _ {Aset : SET a} where
  
    open import Partiality-monad.Inductive
    open import Partiality-monad.Inductive.Alternative-order
    open import Partiality-monad.Inductive.Properties

    -- a slightly more convenient form (for A set) of the library lemma
    now⊑now→≡ : {x y : proj₁ Aset} → (now x ⊑ now y) → x ≡ y
    now⊑now→≡ nn = ∥∥-rec (proj₂ Aset _ _) Prelude.id (_≃_.to (now⊑now≃∥≡∥ ua) nn)
    
    now-injective : {x y : proj₁ Aset} → now x ≡ now y → x ≡ y
    now-injective {x} {y} nowx≡nowy = now⊑now→≡ (subst (λ z → now x ⊑ z) nowx≡nowy (⊑-refl _))

    -- TODO: the two above should be used a couple of times below instead of the unfolded versions

    termination-value-unique : (x : (proj₁ Aset) ⊥) → (a b : (proj₁ Aset)) → x ⇓ a → x ⇓ b → a ≡ b
    termination-value-unique x a b x⇓a x⇓b =
      ∥∥-rec {B = a ≡ b}
            (proj₂ Aset _ _)
            Prelude.id (termination-value-merely-unique ua x⇓a x⇓b) 

    -- TODO: the following should be used to replace some code below a couple of times
    ≡→⊑ : {x y : (proj₁ Aset) ⊥} → x ≡ y → x ⊑ y
    ≡→⊑ refl = ⊑-refl _


open library-stuff


-- TODO: should have used the ⇓-relation



-- my version of monotone sequences. 
module monotone-sequences {Aset : SET a} where

  A = proj₁ Aset
  A-is-set = proj₂ Aset

  -- works only because A is a set, of course.
  MA-is-set : Is-set (Maybe A)
  MA-is-set = ⊎-closure 0 (mono₁ 1 (mono₁ 0 ⊤-contractible)) A-is-set

  -- a predicate stating that a function ℕ → Maybe A is monotone (in a propositional way)
  is-monotone : (f : ℕ → Maybe A) → Set a
  is-monotone f = (n : ℕ) → (f n ≡ f (suc n)) ⊎ f n ≡ nothing × f (suc n) ≢ nothing


  {- this part only works because of the assumption that A is a set.
     The equivalence with Delay A should work more generally (todo: check this claim),
     but it's probably not worth it to emphasize this anyway: As soon as we go to
     A ⊥ we can only work with sets (otherwise, we would have to change the QIIT to a
     HIIT with infinite coherences). -}
  -- surely, there is a more elegant way to do this?!
  abstract
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
  abstract
  
    seq-stable-step : (fp : Seq) (m : ℕ) → (a : A) → (proj₁ fp m ≡ just a) → proj₁ fp (suc m) ≡ just a
    seq-stable-step (f , p) m a fm≡justₐ with p m
    seq-stable-step (f , p) m a fm≡justₐ | inj₁ fm≡fSm = trans (sym fm≡fSm) fm≡justₐ
    seq-stable-step (f , p) m a fm≡justₐ | inj₂ (fm≡nothing , _) = ⊥-elim (⊎.inj₁≢inj₂ (trans (sym fm≡nothing) fm≡justₐ))

    seq-stable : (fp : Seq) (m n : ℕ) → (m ≤ n) → (a : A) → (proj₁ fp m ≡ just a) → proj₁ fp n ≡ just a
    seq-stable (f , p) m n (_≤_.≤-refl′ m≡n) a q = subst (λ k → f k ≡ just a) m≡n q
    seq-stable (f , p) m n (_≤_.≤-step′ {k} m≤k Sk≡n) a q =
      subst (λ o → f o ≡ just a)
            Sk≡n
            (seq-stable-step (f , p) k a (seq-stable (f , p) m k m≤k a q))  

    -- if fn ≡ a and fm ≡ b, then a ≡ b. 
    seq-unique-element : (fp : Seq) (m n : ℕ) (a b : A) → (proj₁ fp m ≡ just a) × (proj₁ fp n ≡ just b) → a ≡ b
    seq-unique-element (f , p) m n a b (fm≡a , fn≡b) with total m n
    seq-unique-element (f , p) m n a b (fm≡a , fn≡b) | inj₁ m≤n = ⊎.cancel-inj₂ (trans (sym (seq-stable (f , p) m n m≤n a fm≡a)) fn≡b) 
    seq-unique-element (f , p) m n a b (fm≡a , fn≡b) | inj₂ n≤m = ⊎.cancel-inj₂ (trans (sym fm≡a) (seq-stable (f , p) n m n≤m b fn≡b))

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
    nothing-just-compare (f , p) a m n fm≡nothing fn≡justₐ | inj₂ ¬Sm≤n =
      ⊥-elim (⊎.inj₁≢inj₂ (trans (sym (smaller-nothing (f , p) n m n≤m fm≡nothing)) fn≡justₐ))
        where
          Sn≤Sm : suc n ≤ suc m
          Sn≤Sm = ≰→> ¬Sm≤n
          n≤m : n ≤ m
          n≤m = suc≤suc⁻¹ Sn≤Sm



-- the ↓ relation: "f ↓ a" should mean that the sequence f "evaluates" to (just a)
module evaluating-sequences {Aset : SET a} where

  open monotone-sequences {Aset} 

  {-
  I define *three* variants of the ↓ relation; f ↓ a says that the sequence f "evaluates" to a.
  The three variants are called _↓_ , _↓'_ , and _∥↓∥_.
  The point is the following:

  (*) _↓_ is the "obvious" definition. It is easy to *use* an element of (f ↓ a).
  (*) _∥↓∥_ is the same, but truncated. It is easier to *construct* an element of (f ∥↓∥ a) because (f ∥↓∥ a) is propositional.
  (*) _↓'_ is an auxiliary definition. It does not use truncation, but is still propositional. It is used to show that _↓_ and _∥↓∥_ are logically equivalent.

  The logical equivalence between the first two definitions justifies that we have more than one:
  We can easily switch between them and use the one which is most convenient in any given situation.

  We could as well have used the theorem that ∥ A ∥ → B is equivalent to weakly constant functions A → B
  (what we do here is basically the unfolded version).
  This would be constant-function≃∥inhabited∥⇒inhabited from the module Truncation.Propositional.
  -}


  _↓_ : Seq → A → Set _
  (f , p) ↓ a = Σ ℕ λ n → f n ≡ just a

  -- ↓ is not propositional, of course. This is not good, and we therefore truncate:
  _∥↓∥_ : Seq → A → Set _
  (f , m) ∥↓∥ a = ∥ (Σ ℕ λ n → f n ≡ just a) ∥ 

  -- Of course, ∥↓∥ is propositional.
  ∥↓∥-is-prop : (fp : Seq) → (a : A) → Is-proposition (fp ∥↓∥ a)
  ∥↓∥-is-prop fp a = truncation-is-proposition

  _↓'_ : Seq → A → Set _
  (f , p) ↓' a = Σ ℕ (λ n → f n ≡ just a × ((n' : ℕ) → (f n' ≢ nothing) → n ≤ n'))

  abstract
  
    -- The point of ↓' is that it is propositional without making use of explicit truncation.
    ↓'-is-prop : (fp : Seq) → (a : A) → Is-proposition (fp ↓' a)
    ↓'-is-prop (f , p) a = Σ-property _ _ (λ _ → ×-closure 1 (MA-is-set _ _)
                                       (Π-closure ext 1 (λ _ → Π-closure ext 1 (λ _ → ≤-propositional)))) number-unique
      where
        number-unique : (x y : (f , p) ↓' a) → proj₁ x ≡ proj₁ y
        number-unique (m , p₁ , p₂) (n , q₁ , q₂) = ≤-antisymmetric (p₂ n (λ e → ⊎.inj₁≢inj₂ (trans (sym e) q₁)))
                                                                    (q₂ m (λ e → ⊎.inj₁≢inj₂ (trans (sym e) p₁)))
    
    -- now: the equivalences
    -- the easy directions are ↓' ⇒ ↓ ⇒ ∥↓∥. The hard implication is ∥↓∥ ⇒ ↓', which we do first: 
    ∥↓∥→↓' : {fp : Seq} → {a : A} → (fp ∥↓∥ a) → (fp ↓' a)
    ∥↓∥→↓' {fp} {a} = ∥∥-rec {B = fp ↓' a} (↓'-is-prop fp a) (λ {(n , fn≡justₐ) → find-min n a fn≡justₐ}) where
  
      f : ℕ → Maybe A
      f = proj₁ fp
      p : is-monotone f
      p = proj₂ fp
        
      find-min : (n : ℕ) → (a : A) → (f n ≡ just a) → fp ↓' a 
      find-min zero    a fn≡justₐ = zero , fn≡justₐ , (λ _ _ → zero≤ _)
      find-min (suc n) a fSn≡justₐ with inspect (f n)
      find-min (suc n) a fSn≡justₐ | nothing , fn≡nothing = suc n , fSn≡justₐ , Sn-is-min
        where
          Sn-is-min : (n' : ℕ) → (f n' ≢ nothing) → suc n ≤ n'
          Sn-is-min n' fn'≢nothing with inspect (f n')
          Sn-is-min n' fn'≢nothing | nothing , fn'≡nothing = ⊥-elim (fn'≢nothing fn'≡nothing)
          Sn-is-min n' fn'≢nothing | just b , fn'≡justb    = nothing-just-compare (f , p) b n n' fn≡nothing fn'≡justb
    
      find-min (suc n) a fSn≡justₐ | just b , fn≡justb with find-min n b fn≡justb
      find-min (suc n) a fSn≡justₐ | just b , fn≡justb | min , fmin≡justb , min-is-min = min , fmin≡justa , min-is-min
        where
          fmin≡justa : f min ≡ just a
          fmin≡justa = subst (λ c → f min ≡ just c) (seq-unique-element (f , p) min (suc n) b a (fmin≡justb , fSn≡justₐ)) fmin≡justb 
    
    
    -- Now, the logical equivalence that we want is easy:
    ↓⇔∥↓∥ : ∀ {fp} {a} → (fp ↓ a) ⇔ (fp ∥↓∥ a)
    ↓⇔∥↓∥ {fp} {a} = record { to = ∣_∣ ;
                             from = ∥↓∥→↓
                           }
      where
        ∥↓∥→↓ : fp ∥↓∥ a → fp ↓ a
        ∥↓∥→↓ fp∥↓∥a with ∥↓∥→↓' {fp} {a} fp∥↓∥a
        ∥↓∥→↓ fp∥↓∥a | n , fn≡justₐ , _ = n , fn≡justₐ


-- A boring, straightforward construction.
module completion-to-seq {Aset : SET a} where

  open monotone-sequences {Aset}
  open evaluating-sequences {Aset} 

  
  -- If we have *any* function f : ℕ → Maybe such that 
  --    (f m ≡ just a) and (f n ≡ just b) imply a ≡ b
  -- then there is a canonical way to complete it to a sequence seq.
  -- We have that f m ≡ just a implies seq m ≡ just a (i.e. "seq is at least f").
  complete-function : (f : ℕ → Maybe A)
                    → ((m n : ℕ) → (a b : A) → (f m ≡ just a) → (f n ≡ just b) → a ≡ b)
                    → Σ Seq
                        λ seq → (a : A) → ((seq ↓ a) ⇔ (Σ ℕ λ j → f j ≡ just a))
  complete-function f q = (take-max , max-is-mon) ,
                          (λ a → record { to = λ {(n , take-maxₙ≡justₐ) → find-preimage n a take-maxₙ≡justₐ} ;
                                          from = λ {(n , fₙ≡justₐ) → n , take-max-greater-f a n fₙ≡justₐ}
                                        })
    where
      take-max : ℕ → Maybe A
      take-max zero    = f zero
      take-max (suc n) = [ (λ _ → take-max n) , (λ a → f (suc n)) ] (f (suc n))

      take-max-greater-f : (a : A) → (k : ℕ) → f k ≡ just a → take-max k ≡ just a
      take-max-greater-f a zero f0≡justₐ = f0≡justₐ
      -- Remark: this "if f (suc n) ≡ just a then take-max n ≡ just a" - thing should probably be abstracted. It appears about three times below.
      take-max-greater-f a (suc k) fSk≡justₐ = trans (cong (λ x → [ (λ _ → take-max k) , (λ _ → f (suc k)) ] x) fSk≡justₐ) fSk≡justₐ

      -- remark: I have removed the m ≤ n part
      find-preimage : (n : ℕ) → (a : A) → (take-max n ≡ just a) → Σ ℕ λ m → f m ≡ just a -- × m ≤ n
      find-preimage zero a take-maxₙ≡justₐ = zero , take-maxₙ≡justₐ -- ,  zero≤ _
      find-preimage (suc n) a take-maxSₙ≡justₐ with inspect (f (suc n))
      find-preimage (suc n) a take-maxSₙ≡justₐ | nothing , fSn≡nothing = preim , fpreim≡justₐ -- , preim≤Sn
        where
          take-maxₙ≡justₐ : take-max n ≡ just a
          take-maxₙ≡justₐ = trans (sym (subst (λ x → take-max (suc n) ≡ [ (λ _ → take-max n) , (λ _ → f (suc n)) ] x) fSn≡nothing refl)) take-maxSₙ≡justₐ
          IH = find-preimage n a take-maxₙ≡justₐ
          preim = proj₁ IH
          fpreim≡justₐ = proj₂ IH
          
      find-preimage (suc n) a  take-maxSₙ≡justₐ | just b , fSn≡justb = suc n , trans fSn≡justb (sym justₐ≡justb) -- , ≤-refl  
        where
          justₐ≡justb : just a ≡ just b
          justₐ≡justb = 
            just a           ≡⟨ sym take-maxSₙ≡justₐ ⟩
            take-max (suc n) ≡⟨ subst (λ x → take-max (suc n) ≡ [ (λ _ → take-max n) , (λ _ → f (suc n)) ] x) fSn≡justb refl ⟩
            f (suc n)        ≡⟨ fSn≡justb ⟩∎ 
            just b           ∎

      max-is-mon : is-monotone take-max
      max-is-mon n with inspect (take-max n) | inspect (f (suc n))

      max-is-mon n | _ | nothing , fSn≡nothing =
        inj₁ (subst (λ x → take-max n ≡ [ (λ _ → take-max n) , (λ a₁ → f (suc n)) ] x) (sym fSn≡nothing) refl)

      max-is-mon n | nothing , take-maxₙ≡nothing | just b , fSn≡justb =
        inj₂ (take-maxₙ≡nothing ,
        (λ exp≡nothing → ⊎.inj₁≢inj₂ (
          trans (trans
            (sym exp≡nothing)
            (cong (λ x → [ (λ _ → take-max n) , (λ a₁ → f (suc n)) ] x) fSn≡justb))
            fSn≡justb
          )))
          
      max-is-mon n | just a , take-maxₙ≡justₐ | just b , fSn≡justb = inj₁ take-maxₙ≡take-maxSₙ
        where
          preim = find-preimage n a take-maxₙ≡justₐ
          k = proj₁ preim
          fk≡justₐ = proj₂ preim
          a≡b : a ≡ b
          a≡b = q k (suc n) a b fk≡justₐ fSn≡justb
          take-maxₙ≡take-maxSₙ =
            take-max n ≡⟨ take-maxₙ≡justₐ ⟩
            just a     ≡⟨ cong just a≡b ⟩
            just b     ≡⟨ sym fSn≡justb ⟩
            f (suc n)  ≡⟨ sym (cong (λ x → [ (λ _ → take-max n) , (λ a₁ → f (suc n)) ] x) fSn≡justb) ⟩∎
            take-max (suc n) ∎ 


module relation-on-Seq {Aset : SET a} where

  open monotone-sequences {Aset}
  open evaluating-sequences {Aset}

  -- auxiliary relations that we will use to define the equivalence relation on sequences
  
  _≲_ : Seq → Seq → Set _
  f ≲ g = (a : A) → (f ∥↓∥ a) → (g ∥↓∥ a)

  abstract
    ≲-is-prop : (f g : Seq) → Is-proposition (f ≲ g)
    ≲-is-prop f g = Π-closure ext 1 (λ a → Π-closure ext 1 (λ _ → ∥↓∥-is-prop g a))

  _~_ : Seq → Seq → Set _
  f ~ g = (f ≲ g) × (g ≲ f)

  abstract
    ~-is-prop : (f g : Seq) → Is-proposition (f ~ g)
    ~-is-prop f g = ×-closure 1 (≲-is-prop f g) (≲-is-prop g f)

  -- quotiented sequences
  Seq/~ : Set _
  Seq/~ = Seq / (λ f g → (f ~ g , ~-is-prop f g))



module monotone-to-QIIT {Aset : SET a} where

  open import Partiality-monad.Inductive 
  open import Partiality-monad.Inductive.Properties

  open monotone-sequences {Aset}
  open evaluating-sequences {Aset}
  open relation-on-Seq {Aset}


  -- Our goal is to define the canonical function from Sequences to the QIIT-partiality monad

  aux : Maybe A → A ⊥ 
  aux nothing  = never
  aux (just a) = now a 

  mon→⊑-pointwise : (x y : Maybe A) → ((x ≡ y) ⊎ x ≡ nothing × y ≢ nothing) → aux x ⊑ aux y
  mon→⊑-pointwise x .x (inj₁ refl) = ⊑-refl _
  mon→⊑-pointwise .nothing y (inj₂ (refl , y≢n)) = never⊑ _

  Seq→Increasing : Seq → Increasing-sequence A
  Seq→Increasing (f , p) = aux ∘ f , (λ n → mon→⊑-pointwise (f n) (f (suc n)) (p n))

  canonical : Seq → A ⊥
  canonical = ⨆ ∘ Seq→Increasing

  abstract
    canonical-≲-⊑ : {fp gq : Seq} → fp ≲ gq → canonical fp ⊑ canonical gq
    canonical-≲-⊑ {fp} {gq} fp≲gq =
      least-upper-bound (Seq→Increasing fp)
                        (canonical gq)
                        cgq-is-ub
                 where

                 f : ℕ → Maybe A 
                 f = proj₁ fp
                 cgq-is-ub : (n : ℕ) → Seq→Increasing fp [ n ] ⊑ canonical gq
                 cgq-is-ub n with inspect (f n)
                 cgq-is-ub n | nothing , fn≡nothing = subst (λ x → x ⊑ _) (cong aux (sym fn≡nothing)) (never⊑ _)
                 cgq-is-ub n | inj₂ a , fn≡justₐ =
                   aux (f n)  ⊑⟨ ≡→⊑ {Aset = Aset} (cong aux (trans fn≡justₐ (sym gkₙ≡justₐ))) ⟩ 
                   aux (g kₙ) ⊑⟨ upper-bound′ (Seq→Increasing gq) (⨆ (Seq→Increasing gq)) (⊑-refl _) kₙ ⟩■
                   ⨆ (Seq→Increasing gq) ■
                   where
                   g : ℕ → Maybe A
                   g = proj₁ gq
                   fp∥↓∥a : fp ∥↓∥ a
                   fp∥↓∥a = ∣ n , fn≡justₐ ∣
                   gq∥↓∥a : gq ∥↓∥ a 
                   gq∥↓∥a = fp≲gq a fp∥↓∥a
                   gq↓a : gq ↓ a
                   gq↓a = _⇔_.from (↓⇔∥↓∥ {gq}) gq∥↓∥a
                   kₙ : ℕ 
                   kₙ = proj₁ gq↓a 
                   gkₙ≡justₐ : g kₙ ≡ just a
                   gkₙ≡justₐ = proj₂ gq↓a 


    canonical-respects-~ : {fp gq : Seq} → fp ~ gq → canonical fp ≡ canonical gq
    canonical-respects-~ (fp≲gq , gq≲fp) = antisymmetry (canonical-≲-⊑ fp≲gq) (canonical-≲-⊑ gq≲fp)

  -- Finally, we can extend the canonical function to the quotient.
  canonical' : Seq/~ → A ⊥
  canonical' = rec {P = A ⊥} canonical canonical-respects-~ ⊥-is-set 

  -- ... and this is really an extension.
  canonical'-is-extension : (fp : Seq) → canonical' (Quotient.HIT.[_] fp) ≡ canonical fp
  canonical'-is-extension fp = {!elim-[]-respects-relation ? !}



module canonical-simple-properties {Aset : SET a} where

  open import Partiality-monad.Inductive 
  open import Partiality-monad.Inductive.Properties
  open import Partiality-monad.Inductive.Alternative-order

  open monotone-sequences {Aset}
  open monotone-to-QIIT {Aset}
  open evaluating-sequences {Aset}


  -- sequence constantly nothing
  const-nothing : Seq
  const-nothing = (λ _ → nothing) , (λ _ → inj₁ refl)

  -- the canonical function maps the constantly nothing sequence to 'never'
  abstract
    canonical-nothing-never : canonical const-nothing ≡ never
    canonical-nothing-never = antisymmetry {x = canonical const-nothing} {y = never}
                                           (least-upper-bound _ never (λ _ → ⊑-refl never))
                                           (never⊑ _)

  -- sequencs constantly just a
  const-seq : (a : A) → Seq
  const-seq  a = (λ _ → just a) , (λ _ → inj₁ refl)

  abstract

    -- the canonical function maps the constantly a sequence to 'now a'
    canonical-const-now : (a : A) → canonical (const-seq a) ≡ now a
    canonical-const-now a = antisymmetry {x = canonical (const-seq a)} {y = now a}
                                         (least-upper-bound _ (now a) (λ _ → ⊑-refl _))
                                         (upper-bound′ (Seq→Increasing (const-seq a)) (canonical (const-seq a)) (⊑-refl _) zero)

    -- An important lemma: _↓_ and canonical_⇓_ are equivalent (logically; the first is not propositional).
    canonical⇓↓ : (a : A) → (seq : Seq) → canonical seq ⇓ a ⇔ (seq ↓ a)
    canonical⇓↓ a seq =
      record { to = ⇓→↓ ;
               from = ↓→⇓
             }
        where
          f : ℕ → Maybe A
          f = proj₁ seq
          f-mon : is-monotone f
          f-mon = proj₂ seq
  
          ⇓→↓ : canonical seq ⇓ a → seq ↓ a
          ⇓→↓ cs⇓a = _⇔_.from (↓⇔∥↓∥ {seq} {a}) (∥∥-map Σn,csₙ⇓a→seq↓a ∥Σn,csₙ⇓a∥ ) 
            where
              ∥Σn,csₙ⇓a∥ : ∥ (Σ ℕ λ n → (Seq→Increasing seq) [ n ] ⇓ a) ∥
              ∥Σn,csₙ⇓a∥ = _≃_.to (⨆⇓≃∥∃⇓∥ ua (Seq→Increasing seq) {a}) cs⇓a 
              Σn,csₙ⇓a→seq↓a : (Σ ℕ λ n → (Seq→Increasing seq [ n ]) ⇓ a) → seq ↓ a
              Σn,csₙ⇓a→seq↓a (n , seqₙ≡nowₐ) with inspect (f n)
              Σn,csₙ⇓a→seq↓a (n , seqₙ≡nowₐ) | nothing , fₙ≡nothing =
                ⊥-elim (now≢never ua a
                                  (now a                     ≡⟨ sym seqₙ≡nowₐ ⟩
                                  (Seq→Increasing seq) [ n ] ≡⟨ refl ⟩
                                  aux (f n)                  ≡⟨ cong aux fₙ≡nothing ⟩∎ 
                                  never ∎))
              Σn,csₙ⇓a→seq↓a (n , seqₙ≡nowₐ) | just b , fₙ≡justb = n , subst (λ c → f n ≡ just c) (sym a≡b) fₙ≡justb
                where
                  nowa≡nowb : now a ≡ now b
                  nowa≡nowb = now a                      ≡⟨ sym seqₙ≡nowₐ ⟩
                              (Seq→Increasing seq) [ n ] ≡⟨ refl ⟩
                              aux (f n)                  ≡⟨ cong aux fₙ≡justb ⟩∎ 
                              now b ∎
                  a≡b : a ≡ b
                  a≡b = now-injective {Aset} nowa≡nowb
  
          ↓→⇓ : seq ↓ a → canonical seq ⇓ a
          ↓→⇓ (n , fₙ≡justₐ) = terminating-element-is-⨆ ua (Seq→Increasing seq) {n = n} {x = a} (cong aux fₙ≡justₐ) 



-- The goal of this module is to show that the canonical function
-- (and thus the extended version of it) is surjective.
module canonical'-surjective {Aset : SET a} where

  open import Partiality-monad.Inductive
  open import Partiality-monad.Inductive.Eliminators
  open import Preimage
  open import Univalence-axiom equality-with-J
  open import Surjection equality-with-J
  open import Bijection equality-with-J
  open import Function-universe equality-with-J

  open import Partiality-monad.Inductive.Alternative-order 
  open import Partiality-monad.Inductive.Properties


  open monotone-to-QIIT {Aset} 
  open monotone-sequences {Aset}
  open canonical-simple-properties {Aset}
  open completion-to-seq {Aset}
  open evaluating-sequences {Aset}


  -- TODO: THIS NEEDS TO BE RE-ORGANISED!
  -- by far too many nested 'where'.
  -- The whole module structures of the whole file need to be fixed.

  canonical-surjective : (Axiom-of-countable-choice a) → Surjective canonical
  canonical-surjective cc =
    ⊥-rec-⊥ {P = λ x → ∥ (Σ Seq λ fp → canonical fp ≡ x) ∥}
      (record { pe = ∣ const-nothing , canonical-nothing-never ∣ ;
                po = λ a → ∣ const-seq a , canonical-const-now a ∣ ;
                pl = use-choice ;
                pp = λ _ → truncation-is-proposition })
    where
      use-choice : (s : Increasing-sequence A)
                 → ((n : ℕ) → ∥ (Σ Seq λ fp → canonical fp ≡ s [ n ]) ∥)
                 → ∥ (Σ Seq λ fp → canonical fp ≡ ⨆ s) ∥
      use-choice s pointwise = ∥∥-map construct (cc pointwise)
        where
          construct : ((m : ℕ) → Σ Seq (λ fp → canonical fp ≡ s [ m ])) → (Σ Seq λ fp → canonical fp ≡ ⨆ s)
          construct pw = seq , seq-correct
            where

              seq-at : (m : ℕ) → Seq
              seq-at m = proj₁ (pw m)

              double-seq : ℕ → ℕ → Maybe A
              double-seq m k = proj₁ (seq-at m) k

              double-seq-unique-A : (a b : A) → (m k m' k' : ℕ)
                                    → double-seq m k ≡ just a
                                    → double-seq  m' k' ≡ just b
                                    → a ≡ b
              double-seq-unique-A a b m k m' k' mk↓a m'k'↓b =
                termination-value-unique {Aset = Aset}
                                         (⨆ s) a b
                                         (⨆s⇓c a m k mk↓a)
                                         (⨆s⇓c b m' k' m'k'↓b)
                where
                  ⨆s⇓c : (c : A) → (l o : ℕ) → double-seq l o ≡ just c → ⨆ s ⇓ c
                  ⨆s⇓c c l o lo↓c =
                    terminating-element-is-⨆ ua s {n = l} {x = c}
                                             (subst (λ z → z ⇓ c)
                                                    (proj₂ (pw l))
                                                    (_⇔_.from (canonical⇓↓ c (seq-at l)) (o , lo↓c)))

              -- We are given a function ℕ → ℕ → Maybe A and want to make a function ℕ → Maybe A out of it.
              -- To do this, we use the lemma ℕ↔ℕ².
              -- Note that we do not use the full equivalence; it would be sufficient to use a split surjection.

              ℕ→ℕ² : ℕ → ℕ × ℕ
              ℕ→ℕ² = _↔_.to ℕ↔ℕ²
              ℕ²→ℕ : ℕ × ℕ → ℕ
              ℕ²→ℕ = _↔_.from ℕ↔ℕ²
              ℕ²→ℕ→ℕ²≡id : (x : ℕ × ℕ) → ℕ→ℕ² (ℕ²→ℕ x) ≡ x
              ℕ²→ℕ→ℕ²≡id = _↔_.right-inverse-of ℕ↔ℕ²

              merge-double-seq : ℕ → Maybe A
              merge-double-seq n = double-seq n₁ n₂
                where
                  n₁ = proj₁ (ℕ→ℕ² n) --proj₁ (_↠_.to ℕ↠ℕ×ℕ n)
                  n₂ = proj₂ (ℕ→ℕ² n) -- (_↠_.to ℕ↠ℕ×ℕ n)

              merged-unique : (n n' : ℕ) → (a b : A)
                              → merge-double-seq n ≡ just a
                              → merge-double-seq n' ≡ just b
                              → a ≡ b
              merged-unique n n' a b n↓a n'↓b =
                double-seq-unique-A a b m k m' k' n↓a n'↓b
                where
                  m  = proj₁ (ℕ→ℕ² n)
                  k  = proj₂ (ℕ→ℕ² n)
                  m' = proj₁ (ℕ→ℕ² n')
                  k' = proj₂ (ℕ→ℕ² n') 
                  
              abstract 
              
                seq : Seq
                seq = proj₁ (complete-function merge-double-seq merged-unique) 

                seq-faithful : (a : A) → ((seq ↓ a) ⇔ (Σ ℕ λ j → merge-double-seq j ≡ just a))
                seq-faithful = proj₂ (complete-function merge-double-seq merged-unique)


              seqₙ⊑some-s : (n : ℕ) → Σ ℕ λ m → aux (proj₁ seq n) ⊑ s [ m ]
              seqₙ⊑some-s n with inspect (proj₁ seq n)
              seqₙ⊑some-s n | nothing , seqₙ≡nothing =
                zero , subst (λ x → aux x ⊑ s [ zero ]) (sym seqₙ≡nothing) (never⊑ (s [ zero ]))  
              seqₙ⊑some-s n | just a , seqₙ≡justₐ =
                k₁ ,
                (aux (proj₁ seq n) ⊑⟨ subst (λ z → aux z ⊑ now a) (sym seqₙ≡justₐ) (⊑-refl _) ⟩
                 now a             ⊑⟨ subst (λ z → now a ⊑ z) (sym s[k₁]⇓a) (⊑-refl _) ⟩■
                 s [ k₁ ] ■)
                where
                  k : ℕ
                  k = proj₁ (_⇔_.to (seq-faithful a) (n , seqₙ≡justₐ))
                  merge-double-seqₖ≡justₐ : merge-double-seq k ≡ just a
                  merge-double-seqₖ≡justₐ = proj₂ (_⇔_.to (seq-faithful a) (n , seqₙ≡justₐ))
                  k₁ = proj₁ (ℕ→ℕ² k)
                  k₂ = proj₂ (ℕ→ℕ² k)
                  seq-at-k₁⇓a : canonical (seq-at k₁) ⇓ a
                  seq-at-k₁⇓a = _≃_.from (⇓≃now⊑ ua {x = canonical (seq-at k₁)} {y = a})
                                         (subst (λ z → z ⊑ canonical (seq-at k₁))
                                                (cong aux merge-double-seqₖ≡justₐ)
                                                (upper-bound′ (Seq→Increasing (seq-at k₁)) _ (⊑-refl _) k₂))
                  s[k₁]⇓a : s [ k₁ ] ⇓ a
                  s[k₁]⇓a = subst (λ z → z ⇓ a) (proj₂ (pw k₁)) seq-at-k₁⇓a 

              cseq⊑⨆s : canonical seq ⊑ ⨆ s
              cseq⊑⨆s = least-upper-bound (Seq→Increasing seq) (⨆ s) (λ n →
                          Seq→Increasing seq [ n ]    ⊑⟨ proj₂ (seqₙ⊑some-s n) ⟩
                          s [ proj₁ (seqₙ⊑some-s n) ] ⊑⟨ upper-bound′ s (⨆ s) (⊑-refl _) _ ⟩■
                          ⨆ s ■)



              -- the sequence that we have now produced is at least seq-at m (if we apply canonical to both).
              seq-at⊑seq : (m : ℕ) → canonical (seq-at m) ⊑ canonical seq
              seq-at⊑seq m =
                least-upper-bound (Seq→Increasing (seq-at m))
                                  (canonical seq)
                                  seq-at-m-k⊑seq
                  where
                    seq-at-m-k⊑seq : (k : ℕ) → Seq→Increasing (seq-at m) [ k ] ⊑ canonical seq
                    seq-at-m-k⊑seq k with inspect (proj₁ (seq-at m) k)
                    seq-at-m-k⊑seq k | nothing , seq-at-m-k≡nothing =
                      subst (λ z → aux z ⊑ canonical seq) (sym seq-at-m-k≡nothing) (never⊑ _)
                    seq-at-m-k⊑seq k | just a , seq-at-m-k≡justₐ    = 
                      ≡→⊑ {Aset = Aset}
                          {x = Seq→Increasing (seq-at m) [ k ]}
                          {y = canonical seq}
                            (Seq→Increasing (seq-at m) [ k ] ≡⟨ cong aux seq-at-m-k≡justₐ ⟩
                            now a ≡⟨ sym (_⇔_.from (canonical⇓↓ a seq) seq↓a) ⟩∎
                            canonical seq ∎) 
                      where
                        n : ℕ 
                        n = ℕ²→ℕ (m , k)
                        n₁,n₂ = ℕ→ℕ² n 
                        n₁ = proj₁ n₁,n₂
                        n₂ = proj₂ n₁,n₂
                        n₁,n₂≡m,k : n₁,n₂ ≡ (m , k)
                        n₁,n₂≡m,k = ℕ²→ℕ→ℕ²≡id (m , k)
                        -- remark: the above with (n₁ , n₂) instead of n₁,n₂ does not work (becomes yellow).
                        n₁≡m = cong proj₁ n₁,n₂≡m,k
                        n₂≡k = cong proj₂ n₁,n₂≡m,k

                        merge-double-seqₙ≡justₐ : merge-double-seq n ≡ just a
                        merge-double-seqₙ≡justₐ = 
                          merge-double-seq n ≡⟨ refl ⟩
                          double-seq n₁ n₂   ≡⟨ cong (λ j → double-seq n₁ j) n₂≡k ⟩ 
                          double-seq n₁ k    ≡⟨ cong (λ j → double-seq j k) n₁≡m ⟩ 
                          double-seq m k     ≡⟨ seq-at-m-k≡justₐ ⟩∎ 
                          just a ∎  

                        seq↓a : seq ↓ a
                        seq↓a = _⇔_.from (seq-faithful a) (n , merge-double-seqₙ≡justₐ)

              ⨆s⊑csq : ⨆ s ⊑ canonical seq
              ⨆s⊑csq = least-upper-bound s (canonical seq) (λ n → 
                s [ n ]              ⊑⟨ ≡→⊑ {Aset = Aset} (sym (proj₂ (pw n))) ⟩
                canonical (seq-at n) ⊑⟨ seq-at⊑seq n ⟩■
                canonical seq        ■)

              seq-correct : canonical seq ≡ ⨆ s
              seq-correct = antisymmetry {x = canonical seq} {y = ⨆ s} cseq⊑⨆s ⨆s⊑csq

  canonical'-surjective : (Axiom-of-countable-choice a) → Surjective canonical'
  canonical'-surjective cc z =
    ∥∥-map (λ { (pre , can-pre≡z) → Quotient.HIT.[_] pre , trans (canonical'-is-extension pre) can-pre≡z })
          (canonical-surjective cc z)


-- canonical' is injective
module canonical'-injective {Aset : SET a} where

  open import Partiality-monad.Inductive
  open import Partiality-monad.Inductive.Eliminators
  open import Preimage
  open import Univalence-axiom equality-with-J
  open import Surjection equality-with-J
  open import Injection equality-with-J

  open import Partiality-monad.Inductive.Alternative-order hiding (_≲_)
  open import Partiality-monad.Inductive.Properties


  open monotone-to-QIIT {Aset} 
  open monotone-sequences {Aset}
  open canonical-simple-properties {Aset}
  open completion-to-seq {Aset}
  open evaluating-sequences {Aset}
  open relation-on-Seq {Aset}

  canonical-semi : {f g : Seq} → canonical f ⊑ canonical g → f ≲ g
  canonical-semi {f} {g} cf⊑cg a ∥f↓a∥ = _⇔_.to (↓⇔∥↓∥ {fp = g}) (_⇔_.to (canonical⇓↓ a g) canonicalg⇓a)
    where
      canonicalf⇓a : canonical f ⇓ a
      canonicalf⇓a = _⇔_.from (canonical⇓↓ a f) (_⇔_.from (↓⇔∥↓∥ {fp = f}) ∥f↓a∥)
      canonicalg⇓a : canonical g ⇓ a
      canonicalg⇓a = _≃_.from (⇓≃now⊑ ua {x = canonical g} {y = a}) (
                              now a ⊑⟨ ≡→⊑ {Aset = Aset} (sym canonicalf⇓a) ⟩
                              canonical f ⊑⟨ cf⊑cg ⟩■
                              canonical g ■)

  ~←canonical≡ : {f g : Seq} → canonical f ≡ canonical g → f ~ g
  ~←canonical≡ {f} {g} cf≡cg = (canonical-semi {f} {g} (≡→⊑ {Aset = Aset} cf≡cg ))
                               ,
                               (canonical-semi {g} {f} (≡→⊑ {Aset = Aset} (sym cf≡cg)))

  -- We do the "double-induction" in two steps.
  -- First auxiliary step:
  can-inj-elim₁ : {f : Seq} → {g' : Seq/~} → canonical f ≡ canonical' g' → Quotient.HIT.[_] f ≡ g'
  can-inj-elim₁ {f} {g'} =
    quot-elim-prop
      (λ g' → canonical f ≡ canonical' g' → Quotient.HIT.[_] f ≡ g')
      (λ g → λ cfcg → []-respects-relation (~←canonical≡ (trans cfcg (canonical'-is-extension g)))) 
      (λ _ → Π-closure ext 1 (λ _ → /-is-set _ _))
      g'

  -- Second step - this is what we want:
  canonical'-injective : Injective canonical' 
  canonical'-injective {f'} {g'} =
    quot-elim-prop
      (λ f' → canonical' f' ≡ canonical' g' → f' ≡ g')
      (λ f cfcg → can-inj-elim₁ (trans (sym (canonical'-is-extension f)) cfcg) )
      (λ _ → Π-closure ext 1 (λ _ → /-is-set _ _))
      f'


-- canonical' is an equivalence: needs a library lemma which (I think) is not there yet.
module canonical'-equivalence {Aset : SET a} where

  open import Partiality-monad.Inductive.Properties {a} {proj₁ Aset}
  open monotone-to-QIIT {Aset} 
  open canonical'-surjective
  open canonical'-injective

  canonical'-equiv : (Axiom-of-countable-choice a) → Is-equivalence (canonical')
  canonical'-equiv cc = InjSurj→≃ {Yset = _ , ⊥-is-set} canonical' canonical'-injective (canonical'-surjective cc)


{-
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



-}
