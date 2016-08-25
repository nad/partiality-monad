------------------------------------------------------------------------
-- The syntax of, and a type system for, the untyped λ-calculus with
-- constants
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Lambda.Syntax where

open import Equality.Propositional
open import Prelude

open import Maybe equality-with-J

------------------------------------------------------------------------
-- Terms

-- Variables are represented using de Bruijn indices.

infixl 9 _·_

data Tm (n : ℕ) : Set where
  con : (i : ℕ) → Tm n
  var : (x : Fin n) → Tm n
  ƛ   : Tm (suc n) → Tm n
  _·_ : Tm n → Tm n → Tm n

------------------------------------------------------------------------
-- Vectors

-- Vectors.

Vec : ∀ {a} → Set a → ℕ → Set a
Vec A n = Fin n → A

-- An empty vector.

empty : ∀ {a} {A : Set a} → Vec A 0
empty ()

-- Adds one element to a vector.

snoc : ∀ {a} {A : Set a} {n} → Vec A n → A → Vec A (suc n)
snoc xs x = [ const x , xs ]

------------------------------------------------------------------------
-- Closure-based definition of values

-- Environments and values. Defined in a module parametrised by the
-- type of terms.

module Closure (Tm : ℕ → Set) where

  mutual

    -- Environments.

    Env : ℕ → Set
    Env n = Vec Value n

    -- Values. Lambdas are represented using closures, so values do
    -- not contain any free variables.

    data Value : Set where
      con : (i : ℕ) → Value
      ƛ   : ∀ {n} (t : Tm (suc n)) (ρ : Env n) → Value

------------------------------------------------------------------------
-- Type system

-- Recursive, simple types, defined coinductively.

infixr 8 _⇾_

mutual

  data Ty : Set where
    nat : Ty
    _⇾_ : (σ τ : ∞Ty) → Ty

  record ∞Ty : Set where
    coinductive
    constructor [_]
    field
      force : Ty

open ∞Ty public

-- Contexts.

Ctxt : ℕ → Set
Ctxt n = Vec Ty n

-- Type system.

infix 4 _⊢_∈_

data _⊢_∈_ {n} (Γ : Ctxt n) : Tm n → Ty → Set where
  con : ∀ {i} → Γ ⊢ con i ∈ nat
  var : ∀ {x} → Γ ⊢ var x ∈ Γ x
  ƛ   : ∀ {t σ τ} →
        snoc Γ (force σ) ⊢ t ∈ force τ → Γ ⊢ ƛ t ∈ σ ⇾ τ
  _·_ : ∀ {t₁ t₂ σ τ} →
        Γ ⊢ t₁ ∈ σ ⇾ τ → Γ ⊢ t₂ ∈ force σ →
        Γ ⊢ t₁ · t₂ ∈ force τ

------------------------------------------------------------------------
-- Some definitions used in several type soundness proofs

open Closure Tm

-- WF-Value, WF-Env and WF-MV specify when a
-- value/environment/potential value is well-formed with respect to a
-- given context (and type).

mutual

  data WF-Value : Ty → Value → Set where
    con : ∀ {i} → WF-Value nat (con i)
    ƛ   : ∀ {n Γ σ τ} {t : Tm (1 + n)} {ρ} →
          snoc Γ (force σ) ⊢ t ∈ force τ →
          WF-Env Γ ρ →
          WF-Value (σ ⇾ τ) (ƛ t ρ)

  WF-Env : ∀ {n} → Ctxt n → Env n → Set
  WF-Env Γ ρ = ∀ x → WF-Value (Γ x) (ρ x)

WF-MV : Ty → Maybe Value → Set
WF-MV σ v = maybe (WF-Value σ) Prelude.⊥ v

-- Some "constructors" for WF-Env.

empty-wf : WF-Env empty empty
empty-wf ()

snoc-wf : ∀ {n} {Γ : Ctxt n} {ρ σ v} →
          WF-Env Γ ρ → WF-Value σ v → WF-Env (snoc Γ σ) (snoc ρ v)
snoc-wf ρ-wf v-wf fzero    = v-wf
snoc-wf ρ-wf v-wf (fsuc x) = ρ-wf x

------------------------------------------------------------------------
-- Example

-- A non-terminating term.

ω : Tm 0
ω = ƛ (var fzero · var fzero)

Ω : Tm 0
Ω = ω · ω

-- Ω is well-typed.

Ω-well-typed : (τ : Ty) → empty ⊢ Ω ∈ τ
Ω-well-typed τ =
  _·_ {σ = σ} {τ = [ τ ]} (ƛ (var · var)) (ƛ (var · var))
  where
  σ : ∞Ty
  force σ = σ ⇾ [ τ ]

-- A call-by-value fixpoint combinator.

Z : Tm 0
Z = ƛ (t · t)
  where
  t = ƛ (var (fsuc fzero) ·
         ƛ (var (fsuc fzero) · var (fsuc fzero) · var fzero))

-- This combinator is also well-typed.

Z-well-typed :
  ∀ {σ τ} →
  empty ⊢ Z ∈ [ [ [ σ ] ⇾ [ τ ] ] ⇾ [ [ σ ] ⇾ [ τ ] ] ] ⇾
              [ [ σ ] ⇾ [ τ ] ]
Z-well-typed {σ = σ} {τ = τ} =
  ƛ (_·_ {σ = υ} {τ = [ _ ]}
         (ƛ (var · ƛ (var · var · var)))
         (ƛ (var · ƛ (var · var · var))))
  where
  υ : ∞Ty
  force υ = υ ⇾ [ [ σ ] ⇾ [ τ ] ]
