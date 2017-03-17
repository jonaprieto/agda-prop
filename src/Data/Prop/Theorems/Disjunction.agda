------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ∨ connective.
------------------------------------------------------------------------


open import Data.Nat using (ℕ)

module Data.Prop.Theorems.Disjunction (n : ℕ) where

open import Data.Prop.Syntax n
open import Data.Prop.Theorems.Implication n using (th244e)

open import Function using (_$_)


∨-dist₁ : ∀ {Γ} {φ ψ ω}
        → Γ ⊢ φ ∨ (ψ ∧ ω)
        → Γ ⊢ (φ ∨ ψ) ∧ (φ ∨ ω)


lem1 : ∀ {Γ} {φ ψ}
     → Γ ⊢ ¬ ¬ φ ∨ ¬ ¬ ψ
     → Γ ⊢ φ ∨ ψ

lem2 : ∀ {Γ} {φ ψ}
     → Γ ⊢ (φ ∨ ψ) ∧ ¬ ψ
     → Γ ⊢ φ



postulate
  ∨-equiv : ∀ {Γ} {φ ψ}
          → Γ ⊢ φ ∨ ψ
          → Γ ⊢ ¬ (¬ φ ∧ ¬ ψ)

  ∨-comm  : ∀ {Γ} {φ ψ}
          → Γ ⊢ φ ∨ ψ
          → Γ ⊢ ψ ∨ φ

  ∨-assoc₁ : ∀ {Γ} {φ ψ ρ}
          → Γ ⊢ (φ ∨ ψ) ∨ ρ
          → Γ ⊢ φ ∨ (ψ ∨ ρ)

  ∨-assoc₂ : ∀ {Γ} {φ ψ ρ}
          → Γ ⊢ φ ∨ (ψ ∨ ρ)
          → Γ ⊢ (φ ∨ ψ) ∨ ρ



  ∨-dist₂ : ∀ {Γ} {φ ψ ω}
          → Γ ⊢ (φ ∨ ω) ∧ (ψ ∨ ω)
          → Γ ⊢ (φ ∧ ψ) ∨ ω

  ∨-morgan₁ : ∀ {Γ} {φ ψ}
            → Γ ⊢ ¬ (φ ∨ ψ) ⇒ ¬ φ ∧ ¬ ψ

  ∨-morgan₂ : ∀ {Γ} {φ ψ}
            → Γ ⊢ ¬ φ ∧ ¬ ψ
            → Γ ⊢ ¬ (φ ∨ ψ)

------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------

∨-dist₁ {Γ}{φ}{ψ}{ω} =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∧-intro
          (∨-intro₁ ψ (assume {Γ = Γ} φ))
          (∨-intro₁ ω (assume {Γ = Γ} φ)))
        (∧-intro
          (∨-intro₂ φ (∧-proj₁ (assume {Γ = Γ} (ψ ∧ ω))))
          (∨-intro₂ φ (∧-proj₂ (assume {Γ = Γ} (ψ ∧ ω)))))))

lem1 {Γ}{φ}{ψ} =
  ⇒-elim $
    ⇒-intro $
      ∨-elim {Γ = Γ}
        (∨-intro₁ ψ $
          ⇒-elim th244e $ assume {Γ = Γ} $ ¬ ¬ φ)
        (∨-intro₂ φ $
          ⇒-elim th244e $ assume {Γ = Γ} $ ¬ ¬ ψ)


lem2 {Γ}{φ}{ψ} seq =
  ⇒-elim
    (⇒-intro $
      (∨-elim {Γ = Γ}
        (assume {Γ = Γ} φ)
        (⊥-elim φ
          (¬-elim
            (weaken ψ (∧-proj₂ seq))
            (assume {Γ = Γ} ψ)))))
    (∧-proj₁ seq)
