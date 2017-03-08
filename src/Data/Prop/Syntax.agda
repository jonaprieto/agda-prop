-- Syntax.agda module

open import Data.Nat using (ℕ; zero; suc)

module Data.Prop.Syntax (n : ℕ) where

open import Data.Bool renaming (_∧_ to _&&_; _∨_ to _||_)
open import Data.Bool using (Bool; true; false; not)
open import Data.Fin  using (Fin; zero; suc; #_)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Vec  using (Vec; lookup)

open import Function  using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

Type = Set

------------------------------------------------------------------------------
-- Proposition data type.
------------------------------------------------------------------------------

data Prop : Type where
  Var              : Fin n → Prop
  ⊤                : Prop
  ⊥                : Prop
  _∧_ _∨_ _⇒_ _⇔_ : (φ ψ : Prop) → Prop
  ¬_               : (φ : Prop) → Prop

-- Precedence of operators
infix  11 ¬_
infixl 8 _∧_ _∨_
infixr 7 _⇒_ _⇔_

------------------------------------------------------------------------------
-- Context: list (set) of hypotesis and axioms.
------------------------------------------------------------------------------
Ctxt : Type
Ctxt = List Prop

infixl 5 _,_
_,_ : Ctxt → Prop → Ctxt
Γ , φ =  Γ ++ [ φ ]

∅ : Ctxt
∅ = []

infix 30 _⨆_
_⨆_ : Ctxt → Ctxt → Ctxt
Γ ⨆ Δ = Γ ++ Δ

infix 4 _∈_
data _∈_ (φ : Prop) : Ctxt → Type where
  here  : ∀ {Γ} → φ ∈ Γ , φ
  there : ∀ {Γ} → (ψ : Prop) → φ ∈ Γ → φ ∈ Γ , ψ
  ⨆-ext : ∀ {Γ} → (Δ : Ctxt) → φ ∈ Γ → φ ∈ Γ ⨆ Δ

_⊆_ : Ctxt → Ctxt → Type
Γ ⊆ Η = ∀ {φ} → φ ∈ Γ → φ ∈ Η

------------------------------------------------------------------------------
-- Theorem data type.
------------------------------------------------------------------------------

infix 3 _⊢_
data _⊢_ : (Γ : Ctxt)(φ : Prop) → Type where
-- Hyp.
  assume   : ∀ {Γ} → (φ : Prop)           → Γ , φ ⊢ φ

  axiom    : ∀ {Γ} → (φ : Prop)           → φ ∈ Γ
                                          → Γ ⊢ φ

  weaken   : ∀ {Γ} {φ} → (ψ : Prop)       → Γ ⊢ φ
                                          → Γ , ψ ⊢ φ
-- Top and Bottom.
  ⊤-intro  : ∀ {Γ}                        → Γ ⊢ ⊤

  ⊥-elim   : ∀ {Γ} → (φ : Prop)           → Γ ⊢ ⊥
                                          → Γ ⊢ φ
-- Negation.
  ¬-intro  : ∀ {Γ} {φ}                    → Γ , φ ⊢ ⊥
                                          → Γ ⊢ ¬ φ

  ¬-elim   : ∀ {Γ} {φ}                    → Γ ⊢ ¬ φ → Γ ⊢ φ
                                          → Γ ⊢ ⊥
-- Conjunction.
  ∧-intro  : ∀ {Γ} {φ ψ}                  → Γ ⊢ φ → Γ ⊢ ψ
                                          → Γ ⊢ φ ∧ ψ

  ∧-proj₁  : ∀ {Γ} {φ ψ}                  → Γ ⊢ φ ∧ ψ
                                          → Γ ⊢ φ

  ∧-proj₂  : ∀ {Γ} {φ ψ}                  → Γ ⊢ φ ∧ ψ
                                          → Γ ⊢ ψ
-- Disjunction.
  ∨-intro₁ : ∀ {Γ} {φ} → (ψ : Prop)       → Γ ⊢ φ
                                          → Γ ⊢ φ ∨ ψ

  ∨-intro₂ : ∀ {Γ} {ψ} → (φ : Prop)       → Γ ⊢ ψ
                                          → Γ ⊢ φ ∨ ψ

  ∨-elim  : ∀ {Γ} {φ ψ χ}                 → Γ , φ ⊢ χ
                                          → Γ , ψ ⊢ χ
                                          → Γ , φ ∨ ψ ⊢ χ
-- Implication.
  ⇒-intro  : ∀ {Γ} {φ ψ}                  → Γ , φ ⊢ ψ
                                          → Γ ⊢ φ ⇒ ψ

  ⇒-elim   : ∀ {Γ} {φ ψ}                  → Γ ⊢ φ ⇒ ψ → Γ ⊢ φ
                                          → Γ ⊢ ψ
-- Biconditional.
  ⇔-intro  : ∀ {Γ} {φ ψ}                  → Γ , φ ⊢ ψ
                                          → Γ , ψ ⊢ φ
                                          → Γ ⊢ φ ⇔ ψ

  ⇔-elim₁ : ∀ {Γ} {φ ψ}                  → Γ ⊢ φ → Γ ⊢ φ ⇔ ψ
                                          → Γ ⊢ ψ

  ⇔-elim₂ : ∀ {Γ} {φ ψ}                   → Γ ⊢ ψ → Γ ⊢ φ ⇔ ψ
                                          →  Γ ⊢ φ

------------------------------------------------------------------------------
postulate
    PEM   : ∀ {Γ} {φ}                       → Γ ⊢ φ ∨ ¬ φ

    RAA   : ∀ {Γ} {φ}                       → Γ , ¬ φ ⊢ ⊥
                                            → Γ ⊢ φ
    weaken-Δ₁ : ∀ {Γ} {φ} → (Δ : Ctxt)      → Γ ⊢ φ
                                            → Γ ⨆ Δ ⊢ φ

    weaken-Δ₂ :  ∀ {Γ} {φ} → (Δ : Ctxt)     → Γ ⊢ φ
                                            → Δ ⨆ Γ ⊢ φ
