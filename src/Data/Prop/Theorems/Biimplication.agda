------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ⇔ connective.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)


module Data.Prop.Theorems.Biimplication (n : ℕ) where

open import Data.Prop.Syntax n
open import Function using (_$_)

postulate

  bicon₀ : ∀ {Γ} {φ ψ}
          → Γ ⊢ φ ⇔ ψ
          → Γ ⊢ ¬ φ
          → Γ ⊢ ¬ ψ


  bicon₁ : ∀ {Γ} {φ ψ}
          → Γ ⊢ ¬ φ ⇔ ψ
          → Γ ⊢ φ
          → Γ ⊢ ¬ ψ
