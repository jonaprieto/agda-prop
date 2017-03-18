------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ⇒ connective.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)

module Data.Prop.Theorems.Implication (n : ℕ) where

open import Data.Prop.Syntax n
open import Function using (_$_)


⇒-equiv : ∀ {Γ} {φ ψ}
        → Γ ⊢ φ ⇒ ψ
        → Γ ⊢ ¬ φ ∨ ψ


-- van Dalen 4th Edition. Chapter 2. Section 2.4.
-- Theorem 2.4.4

th244a  : ∀ {Γ} {φ ψ}
        → Γ ⊢ φ ⇒ (ψ ⇒ φ)

th244b  : ∀ {Γ} {φ ψ}
        → Γ ⊢ φ ⇒ (¬ φ ⇒ ψ)

th244c  : ∀ {Γ} {φ ψ ω}
        → Γ ⊢ (φ ⇒ ψ) ⇒ ((ψ ⇒ ω) ⇒ (φ ⇒ ω))

th244d  : ∀ {Γ} {φ ψ}
        → Γ ⊢ (¬ ψ ⇒ ¬ φ) ⇒ (φ ⇒ ψ)

th244e : ∀ {Γ} {φ}
       → Γ ⊢ ¬ (¬ φ) ⇒ φ


impl-15 : ∀ {Γ} {φ ψ ω}
        → Γ ⊢ (φ ∧ ψ) ⇒ ω
        → Γ ⊢ φ ⇒ (ψ ⇒ ω)

postulate
  ⇒-neg   : ∀ {Γ} {φ ψ}
          → Γ ⊢ ¬ (φ ⇒ ψ)
          → Γ ⊢ φ ∧ ¬ ψ

------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------

⇒-equiv {Γ} {φ}{ψ} seq =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₂ (¬ φ)
          (⇒-elim
            (weaken φ seq)
            (assume {Γ = Γ} φ)))
        (∨-intro₁ ψ
          (assume {Γ = Γ} (¬ φ)))))
      PEM

th244a {Γ}{φ}{ψ} =
  ⇒-intro $
    ⇒-intro $
      weaken {φ = φ} ψ $
        assume {Γ = Γ} φ


th244b {Γ}{φ}{ψ} =
  ⇒-intro $
    ⇒-intro $
      ⊥-elim {Γ = (Γ , φ , ¬ φ)} ψ $
        ¬-elim
          (assume  {Γ = Γ , φ} (¬ φ))
          (weaken (¬ φ) (assume {Γ = Γ} φ))


th244c {Γ}{φ}{ψ}{ω} =
  ⇒-intro $
    ⇒-intro $
      ⇒-intro $
        ⇒-elim
          (weaken φ $
            assume {Γ = Γ , φ ⇒ ψ} $ ψ ⇒ ω)
          (⇒-elim
            (weaken φ $
              weaken (ψ ⇒ ω) $
                assume {Γ = Γ} $ φ ⇒ ψ)
            (assume {Γ = Γ , φ ⇒ ψ , ψ ⇒ ω} φ))


th244d {Γ}{φ}{ψ} =
  ⇒-intro $
    ⇒-intro $
      RAA $
        ¬-elim
          (⇒-elim
            (weaken (¬ ψ) $
              weaken φ $
                assume {Γ = Γ} $ ¬ ψ  ⇒ ¬ φ)
            (assume {Γ = Γ , ¬ ψ ⇒ ¬ φ , φ} $ ¬ ψ))
          (weaken (¬ ψ) $
            assume {Γ = Γ , ¬ ψ ⇒ ¬ φ} φ)


th244e {Γ}{φ} =
  ⇒-intro $ RAA
    (¬-elim
      (weaken (¬ φ) $
        assume {Γ = Γ} $ ¬ (¬ φ))
      (assume {Γ = Γ , ¬ (¬ φ)} $ ¬ φ))

impl-15 {Γ}{φ}{ψ}{ω} seq =
  ⇒-intro
    (⇒-intro
      (⇒-elim
        (weaken ψ (weaken φ seq))
        (∧-intro
          (weaken ψ (assume {Γ = Γ} φ))
          (assume {Γ = Γ , φ} ψ))))
