------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ⇒ connective.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.Theorems.Implication ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Function using ( _$_ )

------------------------------------------------------------------------------

⇒-equiv
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ⇒ ψ
  → Γ ⊢ ¬ φ ∨ ψ
⇒-to-¬∨ = ⇒-equiv

-- Theorems from the book:
-- van Dalen 4th Edition. Chapter 2. Section 2.4.

vanDalen244a
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ⇒ (ψ ⇒ φ)

vanDalen244b
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ⇒ (¬ φ ⇒ ψ)

vanDalen244c
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ (φ ⇒ ψ) ⇒ ((ψ ⇒ ω) ⇒ (φ ⇒ ω))

vanDalen244d
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ ψ ⇒ ¬ φ
  → Γ ⊢ φ ⇒ ψ
¬⇒¬-to-⇒ = vanDalen244d

vanDalen244e
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ (¬ φ) ⇒ φ

strip₁
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ φ ⇒ (ψ ⇒ ω)
  → Γ ⊢ (φ ∧ ψ) ⇒ ω

strip₂
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ (φ ∧ ψ) ⇒ ω
  → Γ ⊢ φ ⇒ (ψ ⇒ ω)

strip
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ (φ ⇒ (ψ ⇒ ω)) ⇔ ((φ ∧ ψ) ⇒ ω)

------------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------------

⇒-equiv {Γ}{φ}{ψ} Γ⊢φ⇒ψ =
  (⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₂ (¬ φ)
          (⇒-elim
            (weaken φ Γ⊢φ⇒ψ)
            (assume {Γ = Γ} φ)))
        (∨-intro₁ ψ
          (assume {Γ = Γ} (¬ φ)))))
      PEM)

vanDalen244a {Γ}{φ}{ψ} =
  (⇒-intro
    (⇒-intro
      (weaken {φ = φ} ψ
        (assume {Γ = Γ} φ))))

vanDalen244b {Γ}{φ}{ψ} =
  ⇒-intro $
    ⇒-intro $
      ⊥-elim {Γ = (Γ , φ , ¬ φ)} ψ $
        ¬-elim
          (assume  {Γ = Γ , φ} (¬ φ))
          (weaken (¬ φ) (assume {Γ = Γ} φ))

vanDalen244c {Γ}{φ}{ψ}{ω} =
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


vanDalen244d {Γ}{φ}{ψ} Γ⊢¬ψ⇒¬φ =
  (⇒-elim
    (⇒-intro $
      (⇒-intro $
        RAA $
          ¬-elim
            (⇒-elim
              (weaken (¬ ψ) $
                weaken φ $
                  assume {Γ = Γ} $ ¬ ψ  ⇒ ¬ φ)
              (assume {Γ = Γ , ¬ ψ ⇒ ¬ φ , φ} $ ¬ ψ))
            (weaken (¬ ψ) $
              assume {Γ = Γ , ¬ ψ ⇒ ¬ φ} φ)))
      Γ⊢¬ψ⇒¬φ)

vanDalen244e {Γ}{φ} =
  ⇒-intro $ RAA
    (¬-elim
      (weaken (¬ φ) $
        assume {Γ = Γ} $ ¬ (¬ φ))
      (assume {Γ = Γ , ¬ (¬ φ)} $ ¬ φ))

strip₁ {Γ}{φ}{ψ}{ω} Γ⊢φ⇒ψ⇒ω =
  ⇒-intro
    (⇒-elim
      (⇒-elim
        (weaken (φ ∧ ψ) Γ⊢φ⇒ψ⇒ω)
        (∧-proj₁ (assume {Γ = Γ} (φ ∧ ψ))))
      (∧-proj₂ (assume {Γ = Γ} (φ ∧ ψ))))

strip₂ {Γ}{φ}{ψ}{ω} Γ⊢φ∧ψ⇒ω =
  ⇒-intro
    (⇒-intro
      (⇒-elim
        (weaken ψ (weaken φ Γ⊢φ∧ψ⇒ω))
        (∧-intro
          (weaken ψ (assume {Γ = Γ} φ))
          (assume {Γ = Γ , φ} ψ))))

strip {Γ}{φ}{ψ}{ω} =
  ⇔-intro
    (strip₁ (assume {Γ = Γ} (φ ⇒ ψ ⇒ ω)))
    (strip₂ (assume {Γ = Γ} (φ ∧ ψ ⇒ ω)))
