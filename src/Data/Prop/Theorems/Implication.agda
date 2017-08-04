------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ⇒ connective.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.Theorems.Implication ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Data.Prop.Theorems.Classical n

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
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ⇒ ψ) ⇒ ((ψ ⇒ γ) ⇒ (φ ⇒ γ))

vanDalen244d
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ ψ ⇒ ¬ φ
  → Γ ⊢ φ ⇒ ψ
¬⇒¬-to-⇒ = vanDalen244d

vanDalen244e
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ (¬ φ) ⇒ φ

⇒⇒-to-∧⇒
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ⇒ (ψ ⇒ γ)
  → Γ ⊢ (φ ∧ ψ) ⇒ γ

∧⇒-to-⇒⇒
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ∧ ψ) ⇒ γ
  → Γ ⊢ φ ⇒ (ψ ⇒ γ)

⇒∧⇒-to-⇒∧
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ⇒ ψ) ∧ (φ ⇒ γ)
  → Γ ⊢ φ ⇒ (ψ ∧ γ)

subst⊢⇒₁
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ γ ⇒ φ
  → Γ ⊢ φ ⇒ ψ
  → Γ ⊢ γ ⇒ ψ

subst⊢⇒₂
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ ψ ⇒ γ
  → Γ ⊢ φ ⇒ ψ
  → Γ ⊢ φ ⇒ γ

⇒-trans
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ⇒ ψ
  → Γ ⊢ ψ ⇒ γ
  → Γ ⊢ φ ⇒ γ

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

vanDalen244c {Γ}{φ}{ψ}{γ} =
  ⇒-intro $
    ⇒-intro $
      ⇒-intro $
        ⇒-elim
          (weaken φ $
            assume {Γ = Γ , φ ⇒ ψ} $ ψ ⇒ γ)
          (⇒-elim
            (weaken φ $
              weaken (ψ ⇒ γ) $
                assume {Γ = Γ} $ φ ⇒ ψ)
            (assume {Γ = Γ , φ ⇒ ψ , ψ ⇒ γ} φ))


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

⇒⇒-to-∧⇒ {Γ}{φ}{ψ}{γ} Γ⊢φ⇒ψ⇒γ =
  ⇒-intro
    (⇒-elim
      (⇒-elim
        (weaken (φ ∧ ψ) Γ⊢φ⇒ψ⇒γ)
        (∧-proj₁ (assume {Γ = Γ} (φ ∧ ψ))))
      (∧-proj₂ (assume {Γ = Γ} (φ ∧ ψ))))

∧⇒-to-⇒⇒ {Γ}{φ}{ψ}{γ} Γ⊢φ∧ψ⇒γ =
  ⇒-intro
    (⇒-intro
      (⇒-elim
        (weaken ψ (weaken φ Γ⊢φ∧ψ⇒γ))
        (∧-intro
          (weaken ψ (assume {Γ = Γ} φ))
          (assume {Γ = Γ , φ} ψ))))

⇒∧⇒-to-⇒∧ {Γ}{φ}{ψ}{γ} Γ⊢⟨φ⇒ψ⟩∧⟨φ⇒γ⟩ =
  ⇒-intro
    (∧-intro
      (⇒-elim (∧-proj₁ (weaken φ Γ⊢⟨φ⇒ψ⟩∧⟨φ⇒γ⟩)) (assume {Γ = Γ} φ))
      (⇒-elim (∧-proj₂ (weaken φ Γ⊢⟨φ⇒ψ⟩∧⟨φ⇒γ⟩)) (assume {Γ = Γ} φ)))

subst⊢⇒₁ {Γ}{φ}{ψ}{γ} Γ⊢ψ⇒γ Γ⊢φ⇒ψ =
  ⇒-intro
    (⇒-elim
      (weaken γ Γ⊢φ⇒ψ)
      (⇒-elim (weaken γ Γ⊢ψ⇒γ) (assume {Γ = Γ} γ)))

subst⊢⇒₂ {Γ}{φ}{ψ}{γ} Γ⊢γ⇒φ Γ⊢φ⇒ψ =
 ⇒-intro
   (⇒-elim
     (weaken φ Γ⊢γ⇒φ)
     (⇒-elim (weaken φ Γ⊢φ⇒ψ) (assume {Γ = Γ} φ)))

⇒-trans {Γ}{φ}{ψ}{γ} Γ⊢φ⇒ψ Γ⊢ψ⇒γ = subst⊢⇒₂ Γ⊢ψ⇒γ Γ⊢φ⇒ψ
