------------------------------------------------------------------------
-- A type soundness result
------------------------------------------------------------------------

{-# OPTIONS --safe --sized-types #-}

module Lambda.Delay-monad.Type-soundness where

open import Equality.Propositional
open import Prelude
open import Prelude.Size

open import Function-universe equality-with-J
open import Maybe equality-with-J
open import Monad equality-with-J
open import Vec.Function equality-with-J

open import Delay-monad.Always
open import Delay-monad.Bisimilarity
open import Delay-monad.Monad

open import Lambda.Delay-monad.Interpreter
open import Lambda.Syntax

open Closure Tm

-- If we can prove □ ∞ (WF-MV σ) (run x), then x does not "go wrong".

does-not-go-wrong : ∀ {σ} {x : M ∞ Value} →
                    □ ∞ (WF-MV σ) (run x) → ¬ x ≈M fail
does-not-go-wrong (now {x = nothing} ())
does-not-go-wrong (now {x = just x} x-wf) ()
does-not-go-wrong (later x-wf)            (laterˡ x↯) =
  does-not-go-wrong (force x-wf) x↯

-- A "constructor" for □ i ∘ WF-MV.

_>>=-wf_ :
  ∀ {i σ τ} {x : M ∞ Value} {f : Value → M ∞ Value} →
  □ i (WF-MV σ) (run x) →
  (∀ {v} → WF-Value σ v → □ i (WF-MV τ) (run (f v))) →
  □ i (WF-MV τ) (MaybeT.run (x >>= f))
x-wf >>=-wf f-wf =
  □->>= x-wf λ { {nothing} ()
               ; {just v}  v-wf → f-wf v-wf
               }

-- Well-typed programs do not "go wrong".

mutual

  ⟦⟧-wf : ∀ {i n Γ} (t : Tm n) {σ} → Γ ⊢ t ∈ σ →
          ∀ {ρ} → WF-Env Γ ρ →
          □ i (WF-MV σ) (run (⟦ t ⟧ ρ))
  ⟦⟧-wf (con i)   con             ρ-wf = now con
  ⟦⟧-wf (var x)   var             ρ-wf = now (ρ-wf x)
  ⟦⟧-wf (ƛ t)     (ƛ t∈)          ρ-wf = now (ƛ t∈ ρ-wf)
  ⟦⟧-wf (t₁ · t₂) (t₁∈ · t₂∈) {ρ} ρ-wf =
    ⟦⟧-wf t₁ t₁∈ ρ-wf >>=-wf λ f-wf →
    ⟦⟧-wf t₂ t₂∈ ρ-wf >>=-wf λ v-wf →
    ∙-wf f-wf v-wf

  ∙-wf : ∀ {i σ τ f v} →
         WF-Value (σ ⇾ τ) f → WF-Value (force σ) v →
         □ i (WF-MV (force τ)) (run (f ∙ v))
  ∙-wf (ƛ t₁∈ ρ₁-wf) v₂-wf =
    later λ { .force → ⟦⟧-wf _ t₁∈ (cons-wf v₂-wf ρ₁-wf) }

type-soundness : ∀ {t : Tm 0} {σ} →
                 nil ⊢ t ∈ σ → ¬ ⟦ t ⟧ nil ≈M fail
type-soundness {t} {σ} =
  nil ⊢ t ∈ σ                      ↝⟨ (λ t∈ → ⟦⟧-wf _ t∈ nil-wf) ⟩
  □ ∞ (WF-MV σ) (run (⟦ t ⟧ nil))  ↝⟨ does-not-go-wrong ⟩□
  ¬ ⟦ t ⟧ nil ≈M fail              □
