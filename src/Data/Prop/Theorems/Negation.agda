
open import Data.Nat using (ℕ; zero; suc)

module Data.Prop.Theorems.Negation (n : ℕ) where

open import Data.Prop.Syntax n
open import Function using (_$_)

postulate
  ¬-equiv : ∀ {Γ} {φ}   → Γ ⊢ ¬ φ
                        → Γ ⊢ φ ⇒ ⊥

  ¬-⊤  : ∀ {Γ}          → Γ ⊢ ¬ ⊤
                        → Γ ⊢ ⊥

  ¬-⊤₂ : ∀ {Γ}          → Γ ⊢ ⊤
                        → Γ ⊢ ¬ ⊥

  ¬-⊥₁ : ∀ {Γ}          → Γ ⊢ ¬ ⊥
                        → Γ ⊢ ⊤

  ¬-⊥₂ : ∀ {Γ}          → Γ ⊢ ⊥
                        → Γ ⊢ ¬ ⊤
