------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ⇔ connective.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.Theorems.Biimplication ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Function using ( _$_ )

------------------------------------------------------------------------------

postulate

  thm-bicon₀ : ∀ {Γ} {φ ψ}
             → Γ ⊢ φ ⇔ ψ
             → Γ ⊢ ¬ φ
             → Γ ⊢ ¬ ψ


  thm-bicon₁ : ∀ {Γ} {φ ψ}
             → Γ ⊢ ¬ φ ⇔ ψ
             → Γ ⊢ φ
             → Γ ⊢ ¬ ψ
