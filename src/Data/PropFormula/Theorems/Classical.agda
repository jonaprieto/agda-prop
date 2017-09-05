------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Classical Propositional Logic.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.PropFormula.Theorems.Classical ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Syntax n

------------------------------------------------------------------------------

postulate
  PEM : ∀ {Γ} {φ}
      → Γ ⊢ φ ∨ ¬ φ

RAA
  : ∀ {Γ} {φ}
  → Γ , ¬ φ ⊢ ⊥
  → Γ ⊢ φ

------------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------------

RAA {Γ}{φ} Γ¬φ⊢⊥ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (assume {Γ = Γ} φ)
        (⊥-elim φ Γ¬φ⊢⊥)))
    PEM