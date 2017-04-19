------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems with different connectives.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.Theorems.Mixies ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Theorems.Biimplication n
  using ( ⇔-¬-to-¬; ⇒-⇔-¬∨ )

open import Data.Prop.Theorems.Disjunction n
  using ( ∨-dmorgan; ∨-dmorgan₁ )

open import Data.Prop.Theorems.Implication n
  using ( vanDalen244e; ⇒-equiv )

open import Data.Prop.Syntax n
open import Function using ( _$_ ; _∘_ )

------------------------------------------------------------------------------

e245b
  : ∀ {Γ Δ} {φ ψ}
  → Γ ⊢ φ → Δ , φ ⊢ ψ
  → Γ ⨆ Δ ⊢ ψ

¬⇒-to-∧¬
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ (φ ⇒ ψ)
  → Γ ⊢ φ ∧ ¬ ψ

------------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------------

e245b {Γ}{Δ} Γ⊢φ Δ,φ⊢ψ =
  ⇒-elim
    (weaken-Δ₂ Γ $ ⇒-intro Δ,φ⊢ψ)
    (weaken-Δ₁ Δ Γ⊢φ)

¬⇒-to-∧¬ {Γ}{φ}{ψ} Γ⊢¬⟪φ⇒ψ⟫ =
  ∧-intro
    (⇒-elim vanDalen244e (∧-proj₁ p2))
    (∧-proj₂ p2)
  where
    p1 : Γ ⊢ ¬ (¬ φ ∨ ψ)
    p1 = ⇔-¬-to-¬ ⇒-⇔-¬∨ Γ⊢¬⟪φ⇒ψ⟫

    p2 : Γ ⊢ ¬ (¬ φ) ∧  ¬ ψ
    p2 = ∨-dmorgan₁ p1
