------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems with different connectives.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.Theorems.Mixies ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Theorems.Biimplication n
  using ( thm-bicon₀; ⇒-∨-equiv )

open import Data.Prop.Theorems.Disjunction n
  using ( ∨-dmorgan; ∨-dmorgan₁ )

open import Data.Prop.Theorems.Implication n
  using ( th244e; ⇒-equiv )

open import Data.Prop.Syntax n
open import Function using ( _$_ ; _∘_ )

------------------------------------------------------------------------------


e245b : ∀ {Γ Δ} {φ ψ}
      → Γ ⊢ φ → Δ , φ ⊢ ψ
      → Γ ⨆ Δ ⊢ ψ


neg-⇒ : ∀ {Γ} {φ ψ}
       → Γ ⊢ ¬ (φ ⇒ ψ)
       → Γ ⊢ φ ∧ ¬ ψ

------------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------------

e245b {Γ}{Δ} seq₁ seq₂ =
  ⇒-elim
    (weaken-Δ₂ Γ $ ⇒-intro seq₂)
    (weaken-Δ₁ Δ seq₁)


neg-⇒ {Γ}{φ}{ψ} seq =
  ∧-intro
    (⇒-elim th244e (∧-proj₁ p2))
    (∧-proj₂ p2)
  where
    p1 : Γ ⊢ ¬ (¬ φ ∨ ψ)
    p1 = thm-bicon₀ ⇒-∨-equiv seq

    p2 : Γ ⊢ ¬ (¬ φ) ∧  ¬ ψ
    p2 = ∨-dmorgan₁ p1

   
