------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ⇒ connective.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.Theorems.Implication ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Function using ( _$_; _∘_; flip )

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

⇒⇒-to-∧⇒
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ φ ⇒ (ψ ⇒ ω)
  → Γ ⊢ (φ ∧ ψ) ⇒ ω

∧⇒-to-⇒⇒
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ (φ ∧ ψ) ⇒ ω
  → Γ ⊢ φ ⇒ (ψ ⇒ ω)

subst⊢⇒₁
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ ω ⇒ φ
  → Γ ⊢ φ ⇒ ψ
  → Γ ⊢ ω ⇒ ψ

subst⊢⇒₂
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ ψ ⇒ ω
  → Γ ⊢ φ ⇒ ψ
  → Γ ⊢ φ ⇒ ω

⇒-trans
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ φ ⇒ ψ
  → Γ ⊢ ψ ⇒ ω
  → Γ ⊢ φ ⇒ ω

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

⇒⇒-to-∧⇒ {Γ}{φ}{ψ}{ω} Γ⊢φ⇒ψ⇒ω =
  ⇒-intro
    (⇒-elim
      (⇒-elim
        (weaken (φ ∧ ψ) Γ⊢φ⇒ψ⇒ω)
        (∧-proj₁ (assume {Γ = Γ} (φ ∧ ψ))))
      (∧-proj₂ (assume {Γ = Γ} (φ ∧ ψ))))

∧⇒-to-⇒⇒ {Γ}{φ}{ψ}{ω} Γ⊢φ∧ψ⇒ω =
  ⇒-intro
    (⇒-intro
      (⇒-elim
        (weaken ψ (weaken φ Γ⊢φ∧ψ⇒ω))
        (∧-intro
          (weaken ψ (assume {Γ = Γ} φ))
          (assume {Γ = Γ , φ} ψ))))

subst⊢⇒₁ {Γ}{φ}{ψ}{ω} Γ⊢ψ⇒ω Γ⊢φ⇒ψ =
  ⇒-intro
    (⇒-elim
      (weaken ω Γ⊢φ⇒ψ)
      (⇒-elim (weaken ω Γ⊢ψ⇒ω) (assume {Γ = Γ} ω)))

subst⊢⇒₂ {Γ}{φ}{ψ}{ω} Γ⊢ω⇒φ Γ⊢φ⇒ψ =
 ⇒-intro
   (⇒-elim
     (weaken φ Γ⊢ω⇒φ)
     (⇒-elim (weaken φ Γ⊢φ⇒ψ) (assume {Γ = Γ} φ)))

⇒-trans {Γ}{φ}{ψ}{ω} Γ⊢φ⇒ψ Γ⊢ψ⇒ω = subst⊢⇒₂ Γ⊢ψ⇒ω Γ⊢φ⇒ψ
