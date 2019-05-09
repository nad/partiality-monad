------------------------------------------------------------------------
-- A type soundness result
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe --sized-types #-}

module Lambda.Partiality-monad.Inductive.Type-soundness where

open import Equality.Propositional
open import Prelude hiding (⊥)
open import Prelude.Size

open import Bijection equality-with-J using (_↔_)
open import Equality.Decision-procedures equality-with-J
open import Equivalence equality-with-J using (_≃_)
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-J as Trunc
open import Maybe equality-with-J
open import Monad equality-with-J
open import Univalence-axiom equality-with-J
open import Vec.Function equality-with-J

open import Partiality-monad.Inductive
open import Partiality-monad.Inductive.Alternative-order
open import Partiality-monad.Inductive.Monad

open import Lambda.Partiality-monad.Inductive.Interpreter
open import Lambda.Syntax

open Closure Tm

-- A propositionally truncated variant of WF-MV.

∥WF-MV∥ : Ty ∞ → Maybe Value → Set
∥WF-MV∥ σ x = ∥ WF-MV σ x ∥

-- If we can prove □ (∥WF-MV∥ σ) (run x), then x does not "go wrong".

does-not-go-wrong : ∀ {σ} {x : M Value} →
                    □ (∥WF-MV∥ σ) (run x) → ¬ x ≡ fail
does-not-go-wrong {σ} {x} always =
  x ≡ fail             ↝⟨ cong MaybeT.run ⟩
  run x ≡ now nothing  ↝⟨ always _ ⟩
  ∥WF-MV∥ σ nothing    ↝⟨ id ⟩
  ∥ ⊥₀ ∥               ↝⟨ _↔_.to (not-inhabited⇒∥∥↔⊥ id) ⟩□
  ⊥₀                   □

-- Some "constructors" for □ ∘ ∥WF-MV∥.

return-wf :
  ∀ {σ v} →
  WF-Value σ v →
  □ (∥WF-MV∥ σ) (MaybeT.run (return v))
return-wf v-wf = □-now truncation-is-proposition ∣ v-wf ∣

_>>=-wf_ :
  ∀ {σ τ} {x : M Value} {f : Value → M Value} →
  □ (∥WF-MV∥ σ) (run x) →
  (∀ {v} → WF-Value σ v → □ (∥WF-MV∥ τ) (run (f v))) →
  □ (∥WF-MV∥ τ) (MaybeT.run (x >>= f))
_>>=-wf_ {σ} {τ} {f = f} x-wf f-wf =
  □->>= (λ _ → truncation-is-proposition) x-wf
    λ { {nothing} → Trunc.rec prop ⊥-elim
      ; {just v}  → Trunc.rec prop f-wf
      }
  where
  prop : ∀ {x} → Is-proposition (□ (∥WF-MV∥ τ) x)
  prop = □-closure 1 (λ _ → truncation-is-proposition)

-- Type soundness.

mutual

  ⟦⟧′-wf : ∀ {n Γ} (t : Tm n) {σ} → Γ ⊢ t ∈ σ →
           ∀ {ρ} → WF-Env Γ ρ →
           ∀ n → □ (∥WF-MV∥ σ) (run (⟦ t ⟧′ ρ n))
  ⟦⟧′-wf (con i)   con             ρ-wf n = return-wf con
  ⟦⟧′-wf (var x)   var             ρ-wf n = return-wf (ρ-wf x)
  ⟦⟧′-wf (ƛ t)     (ƛ t∈)          ρ-wf n = return-wf (ƛ t∈ ρ-wf)
  ⟦⟧′-wf (t₁ · t₂) (t₁∈ · t₂∈) {ρ} ρ-wf n =
     ⟦⟧′-wf t₁ t₁∈ ρ-wf n >>=-wf λ f-wf →
     ⟦⟧′-wf t₂ t₂∈ ρ-wf n >>=-wf λ v-wf →
     ∙-wf f-wf v-wf n

  ∙-wf : ∀ {σ τ f v} →
         WF-Value (σ ⇾ τ) f → WF-Value (force σ) v →
         ∀ n → □ (∥WF-MV∥ (force τ)) (run ((f ∙ v) n))
  ∙-wf (ƛ t₁∈ ρ₁-wf) v₂-wf (suc n) = ⟦⟧′-wf _ t₁∈ (cons-wf v₂-wf ρ₁-wf) n
  ∙-wf (ƛ t₁∈ ρ₁-wf) v₂-wf zero    =         $⟨ □-never ⟩
    □ (∥WF-MV∥ _) never                      ↝⟨ ≡⇒↝ bijection $ cong (□ (∥WF-MV∥ _)) (sym never->>=) ⟩□
    □ (∥WF-MV∥ _) (never >>= return ∘ just)  □

type-soundness : ∀ {t : Tm 0} {σ} →
                 nil ⊢ t ∈ σ → ¬ ⟦ t ⟧ nil ≡ fail
type-soundness {t} {σ} =
  nil ⊢ t ∈ σ                                 ↝⟨ (λ t∈ → ⟦⟧′-wf _ t∈ nil-wf) ⟩
  (∀ n → □ (∥WF-MV∥ σ) (run (⟦ t ⟧′ nil n)))  ↝⟨ □-⨆ (λ _ → truncation-is-proposition) ⟩
  □ (∥WF-MV∥ σ) (run (⟦ t ⟧ nil))             ↝⟨ does-not-go-wrong ⟩□
  ¬ ⟦ t ⟧ nil ≡ fail                          □
