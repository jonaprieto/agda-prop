------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Syntax definitions.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.PropFormula.Syntax ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Bool
  renaming ( _∧_ to _&&_; _∨_ to _||_ )
  using    ( Bool; true; false; not )

open import Data.Fin  using ( Fin; #_ )
open import Data.List using ( List ; [] ; _∷_ ; _++_ ; [_] )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; cong; trans; sym; subst)

------------------------------------------------------------------------------

-- Proposition data type.

data PropFormula : Set where
  Var              : Fin n → PropFormula
  ⊤                : PropFormula
  ⊥                : PropFormula
  _∧_ _∨_ _⇒_ _⇔_  : (φ ψ : PropFormula) → PropFormula
  ¬_               : (φ : PropFormula)   → PropFormula

infix  11 ¬_
infixl 8 _∧_ _∨_
infixr 7 _⇒_ _⇔_

-- Context is a list (set) of hypotesis and axioms.

Ctxt : Set
Ctxt = List PropFormula

infixl 5 _,_
_,_ : Ctxt → PropFormula → Ctxt
Γ , φ = Γ ++ [ φ ]

∅ : Ctxt
∅ = []

infix 30 _⨆_
_⨆_ : Ctxt → Ctxt → Ctxt
Γ ⨆ Δ = Γ ++ Δ

infix 4 _∈_
data _∈_ (φ : PropFormula) : Ctxt → Set where
  here   : ∀ {Γ} → φ ∈ Γ , φ
  there  : ∀ {Γ} → (ψ : PropFormula) → φ ∈ Γ → φ ∈ Γ , ψ
  ⨆-ext  : ∀ {Γ} → (Δ : Ctxt) → φ ∈ Γ → φ ∈ Γ ⨆ Δ

_⊆_ : Ctxt → Ctxt → Set
Γ ⊆ Η = ∀ {φ} → φ ∈ Γ → φ ∈ Η

------------------------------------------------------------------------
-- Theorem data type.

infix 3 _⊢_

data _⊢_ : (Γ : Ctxt)(φ : PropFormula) → Set where

-- Hyp.

  assume   : ∀ {Γ} → (φ : PropFormula)      → Γ , φ ⊢ φ

  axiom    : ∀ {Γ} → (φ : PropFormula)      → φ ∈ Γ
                                            → Γ ⊢ φ

  weaken   : ∀ {Γ} {φ} → (ψ : PropFormula)  → Γ ⊢ φ
                                            → Γ , ψ ⊢ φ

  weaken₂   : ∀ {Γ} {φ} → (ψ : PropFormula) → Γ ⊢ φ
                                            → ψ ∷ Γ ⊢ φ
-- Top and Bottom.

  ⊤-intro  : ∀ {Γ}                          → Γ ⊢ ⊤

  ⊥-elim   : ∀ {Γ} → (φ : PropFormula)      → Γ ⊢ ⊥
                                            → Γ ⊢ φ
-- Negation.

  ¬-intro  : ∀ {Γ} {φ}                      → Γ , φ ⊢ ⊥
                                            → Γ ⊢ ¬ φ

  ¬-elim   : ∀ {Γ} {φ}                      → Γ ⊢ ¬ φ → Γ ⊢ φ
                                            → Γ ⊢ ⊥
-- Conjunction.

  ∧-intro  : ∀ {Γ} {φ ψ}                    → Γ ⊢ φ → Γ ⊢ ψ
                                            → Γ ⊢ φ ∧ ψ

  ∧-proj₁  : ∀ {Γ} {φ ψ}                    → Γ ⊢ φ ∧ ψ
                                            → Γ ⊢ φ

  ∧-proj₂  : ∀ {Γ} {φ ψ}                    → Γ ⊢ φ ∧ ψ
                                            → Γ ⊢ ψ
-- Disjunction.

  ∨-intro₁ : ∀ {Γ} {φ} → (ψ : PropFormula)  → Γ ⊢ φ
                                            → Γ ⊢ φ ∨ ψ

  ∨-intro₂ : ∀ {Γ} {ψ} → (φ : PropFormula)  → Γ ⊢ ψ
                                            → Γ ⊢ φ ∨ ψ

  ∨-elim  : ∀ {Γ} {φ ψ χ}                   → Γ , φ ⊢ χ
                                            → Γ , ψ ⊢ χ
                                            → Γ , φ ∨ ψ ⊢ χ
-- Implication.

  ⇒-intro  : ∀ {Γ} {φ ψ}                    → Γ , φ ⊢ ψ
                                            → Γ ⊢ φ ⇒ ψ

  ⇒-elim   : ∀ {Γ} {φ ψ}                    → Γ ⊢ φ ⇒ ψ → Γ ⊢ φ
                                            → Γ ⊢ ψ
-- Biconditional.

  ⇔-intro  : ∀ {Γ} {φ ψ}                    → Γ , φ ⊢ ψ
                                            → Γ , ψ ⊢ φ
                                            → Γ ⊢ φ ⇔ ψ

  ⇔-elim₁ : ∀ {Γ} {φ ψ}                     → Γ ⊢ φ → Γ ⊢ φ ⇔ ψ
                                            → Γ ⊢ ψ

  ⇔-elim₂ : ∀ {Γ} {φ ψ}                     → Γ ⊢ ψ → Γ ⊢ φ ⇔ ψ
                                            → Γ ⊢ φ

------------------------------------------------------------------------
