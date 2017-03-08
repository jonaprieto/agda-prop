
open import Data.Nat using (ℕ; zero; suc)

module Data.Prop.Theorems.Conjunction (n : ℕ) where

open import Data.Prop.Syntax n
open import Function using (_$_)


∧-comm  : ∀ {Γ} {φ ψ}
        → Γ ⊢ φ ∧ ψ
        → Γ ⊢ ψ ∧ φ

∧-comm {Γ}{φ}{ψ} seq =
  ∧-intro
    (∧-proj₂ seq)
    (∧-proj₁ seq)


postulate
  ∧-dist₁ : ∀ {Γ} {φ ψ ω}
          → Γ ⊢ (φ ∨ ψ) ∧ ω
          → Γ ⊢ (φ ∧ ω) ∨ (ψ ∧ ω)

  ∧-dist₂ : ∀ {Γ} {φ ψ ω}
          → Γ ⊢ (φ ∧ ω) ∨ (ψ ∧ ω)
          → Γ ⊢ (φ ∨ ψ) ∧ ω

--- De Morgan's Law

∧-morgan₁ : ∀ {Γ} {φ ψ}
          → Γ ⊢ ¬ (φ ∧ ψ) ⇒ (¬ φ ∨ ¬ ψ)

∧-morgan₁ {Γ}{φ}{ψ} =
  ⇒-intro $
    RAA $
      ¬-elim
        (weaken (¬ (¬ φ ∨ ¬ ψ)) $
          assume {Γ = Γ} $ ¬ (φ ∧ ψ))
        (∧-intro
          (RAA
            (¬-elim
              (weaken (¬ φ) $
                assume {Γ = Γ , ¬ (φ ∧ ψ)} $ ¬ (¬ φ ∨ ¬ ψ))
              (∨-intro₁ (¬ ψ)
                (assume {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ)} $ ¬ φ))))
          (RAA
            (¬-elim {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ) , ¬ ψ}
              (weaken (¬ ψ) $
                assume {Γ = Γ , ¬ (φ ∧ ψ)} $ ¬ (¬ φ ∨ ¬ ψ))
              (∨-intro₂ (¬ φ)
                (assume {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ)} $ ¬ ψ )))))

postulate
  ∧-morgan₂ : ∀ {Γ} {φ ψ}
            → Γ ⊢ ¬ φ ∨ ¬ ψ
            → Γ ⊢ ¬ (φ ∧ ψ)
