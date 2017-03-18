------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ¬ connective.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)

module Data.Prop.Theorems.Negation (n : ℕ) where

open import Data.Prop.Syntax n
open import Function using (_$_ ; _∘_)


postulate

  ¬-equiv : ∀ {Γ} {φ}
          → Γ ⊢ ¬ φ
          → Γ ⊢ φ ⇒ ⊥

¬-⊤  : ∀ {Γ}
     → Γ ⊢ ¬ ⊤
     → Γ ⊢ ⊥


¬-⊤₂ : ∀ {Γ}
     → Γ ⊢ ⊤
     → Γ ⊢ ¬ ⊥


¬-⊥₁ : ∀ {Γ}
     → Γ ⊢ ¬ ⊥
     → Γ ⊢ ⊤


¬-⊥₂ : ∀ {Γ}
     → Γ ⊢ ⊥
     → Γ ⊢ ¬ ⊤

or-to-impl : ∀ {Γ} {φ ψ}
           → Γ ⊢ ¬ φ ∨ ψ
           → Γ ⊢ φ ⇒ ψ

------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------

¬-⊤ seq = ¬-elim seq ⊤-intro


¬-⊤₂ {Γ} seq = ¬-intro (assume {Γ = Γ} ⊥)


¬-⊥₁ seq = ⊤-intro


¬-⊥₂ = ¬-intro ∘ weaken ⊤


or-to-impl {Γ}{φ}{ψ} =
  ⇒-elim $
     ⇒-intro $
       ∨-elim {Γ = Γ}
         (⇒-intro $
           ⊥-elim {Γ = Γ , ¬ φ , φ} ψ
             (¬-elim
               (weaken φ $
                 assume {Γ = Γ} (¬ φ))
               (assume {Γ = Γ , ¬ φ} φ)))
         (⇒-intro $
           weaken φ $
             assume {Γ = Γ} ψ)
