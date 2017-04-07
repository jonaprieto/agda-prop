------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ⇔ connective.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.Theorems.Biimplication ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Theorems.Negation n using ( ¬-equiv ; ¬-equiv₂ )
open import Data.Prop.Syntax n
open import Function using ( _$_ )

------------------------------------------------------------------------------



thm-bicon₀ : ∀ {Γ} {φ ψ}
           → Γ ⊢ φ ⇔ ψ
           → Γ ⊢ ¬ φ
           → Γ ⊢ ¬ ψ

thm-bicon₁ : ∀ {Γ} {φ ψ}
           → Γ ⊢ ¬ φ ⇔ ψ
           → Γ ⊢ φ
           → Γ ⊢ ¬ ψ

------------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------------

thm-bicon₀ {Γ}{φ}{ψ} φ⇔ψ ¬ψ =
  ¬-equiv₂
    (⇒-intro
      (¬-elim
        (weaken ψ ¬ψ)
      (⇔-elim₂
        (assume {Γ = Γ} ψ)
        (weaken ψ φ⇔ψ))))


thm-bicon₁ {Γ}{φ}{ψ} ¬φ⇔ψ seqφ =
  ¬-equiv₂
    (⇒-intro
      (¬-elim
        (⇔-elim₂
          (assume {Γ = Γ} ψ)
          (weaken ψ ¬φ⇔ψ))
        (weaken ψ seqφ)))


