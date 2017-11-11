------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems with different connectives.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.PropFormula.Theorems.Mixies ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Syntax n
open import Data.PropFormula.Theorems.Classical n
open import Data.PropFormula.Theorems.Biimplication n
  using ( ⇔-¬-to-¬; ⇒-⇔-¬∨ )
open import Data.PropFormula.Theorems.Disjunction n
  using ( ∨-dmorgan; ∨-dmorgan₁ )
open import Data.PropFormula.Theorems.Implication n
  using ( vanDalen244e; ⇒-equiv )
open import Data.PropFormula.Theorems.Weakening n

open import Function using ( _$_ ; _∘_ )

------------------------------------------------------------------------------


-- Theorem.
e245b
  : ∀ {Γ Δ} {φ ψ}
  → Γ ⊢ φ → Δ , φ ⊢ ψ
  → Γ ⨆ Δ ⊢ ψ

-- Proof.
e245b {Γ}{Δ} Γ⊢φ Δ,φ⊢ψ =
  ⇒-elim
    (weaken-Δ₂ Γ $ ⇒-intro Δ,φ⊢ψ)
    (weaken-Δ₁ Δ Γ⊢φ)
-------------------------------------------------------------------------- ∎

-- Theorem.
¬⇒-to-∧¬
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ (φ ⇒ ψ)
  → Γ ⊢ φ ∧ ¬ ψ

-- Proof.
¬⇒-to-∧¬ {Γ}{φ}{ψ} Γ⊢¬⟪φ⇒ψ⟫ =
  ∧-intro
    (⇒-elim vanDalen244e (∧-proj₁ p2))
    (∧-proj₂ p2)
  where
    p1 : Γ ⊢ ¬ (¬ φ ∨ ψ)
    p1 = ⇔-¬-to-¬ ⇒-⇔-¬∨ Γ⊢¬⟪φ⇒ψ⟫

    p2 : Γ ⊢ ¬ (¬ φ) ∧  ¬ ψ
    p2 = ∨-dmorgan₁ p1
-------------------------------------------------------------------------- ∎

-- Theorem.
⇒¬∧¬⇒-to-¬⇔
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ (φ ⇒ ¬ ψ) ∧ (¬ ψ ⇒ φ)
  → Γ ⊢ ¬ (φ ⇔ ψ)

-- Proof.
⇒¬∧¬⇒-to-¬⇔ {Γ} {φ} {ψ} thm =
 ¬-intro
   (¬-elim
     (¬-intro
       (¬-elim
         (⇒-elim
           (weaken ψ (weaken (φ ⇔ ψ) (∧-proj₁ thm)))
           (⇔-elim₂
             (assume {Γ = Γ , φ ⇔ ψ} ψ)
             (weaken ψ (assume {Γ = Γ} (φ ⇔ ψ)))))
         (assume {Γ = Γ , φ ⇔ ψ} ψ)))
    (RAA
      (¬-elim
         (¬-intro
           (¬-elim
             (⇒-elim
               (weaken φ (weaken (¬ ψ ) (weaken (φ ⇔ ψ) (∧-proj₁ thm))))
               (assume {Γ = Γ , φ ⇔ ψ , ¬ ψ} φ))
             (⇔-elim₁
               (assume {Γ = Γ , φ ⇔ ψ , ¬ ψ} φ)
               (weaken φ (weaken (¬ ψ) (assume {Γ = Γ} (φ ⇔ ψ)))))))
         (⇒-elim
           (weaken (¬ ψ) (weaken (φ ⇔ ψ) (∧-proj₂ thm)))
           (assume {Γ = Γ , φ ⇔ ψ} (¬ ψ))))))
-------------------------------------------------------------------------- ∎
