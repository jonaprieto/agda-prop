------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ∨ connective.
------------------------------------------------------------------------


open import Data.Nat using (ℕ)

module Data.Prop.Theorems.Disjunction (n : ℕ) where

open import Data.Prop.Syntax n
open import Data.Prop.Theorems.Implication n using (th244e)

open import Function using (_$_)


∨-assoc₁ : ∀ {Γ} {φ ψ ω}
         → Γ ⊢ (φ ∨ ψ) ∨ ω
         → Γ ⊢ φ ∨ (ψ ∨ ω)


∨-comm  : ∀ {Γ} {φ ψ}
        → Γ ⊢ φ ∨ ψ
        → Γ ⊢ ψ ∨ φ

∨-dist₁ : ∀ {Γ} {φ ψ ω}
        → Γ ⊢ φ ∨ (ψ ∧ ω)
        → Γ ⊢ (φ ∨ ψ) ∧ (φ ∨ ω)


∨-dist₂ : ∀ {Γ} {φ ψ ω}
        → Γ ⊢ (φ ∨ ψ) ∧ (φ ∨ ω)
        → Γ ⊢ φ ∨ (ψ ∧ ω)

∨-morgan₁ : ∀ {Γ} {φ ψ}
          → Γ ⊢ ¬ (φ ∨ ψ)
          → Γ ⊢ ¬ φ ∧ ¬ ψ

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

  ∨-assoc₂ : ∀ {Γ} {φ ψ ρ}
          → Γ ⊢ φ ∨ (ψ ∨ ρ)
          → Γ ⊢ (φ ∨ ψ) ∨ ρ

  ∨-morgan₂ : ∀ {Γ} {φ ψ}
            → Γ ⊢ ¬ φ ∧ ¬ ψ
            → Γ ⊢ ¬ (φ ∨ ψ)

------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------

∨-assoc₁ {Γ}{φ}{ψ}{ω} =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (⇒-elim
          (⇒-intro
            (∨-elim {Γ  = Γ , φ ∨ ψ}
              (∨-intro₁ (ψ ∨ ω)
                (assume {Γ = Γ , φ ∨ ψ} φ))
              (∨-intro₂ φ
                (∨-intro₁ ω
                  (assume {Γ = Γ , φ ∨ ψ} ψ)))))
          (assume {Γ = Γ} (φ ∨ ψ)))
        (∨-intro₂ φ
          (∨-intro₂ ψ
            (assume {Γ = Γ} ω)))))

∨-comm {Γ}{φ}{ψ} =
  ⇒-elim $
    ⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₂ ψ
          (assume {Γ = Γ} φ))
        (∨-intro₁ φ $
           assume {Γ = Γ} ψ))

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

∨-dist₂  {Γ}{φ}{ψ}{ω} seq =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ (ψ ∧ ω) (assume {Γ = Γ} φ))
        (⇒-elim
          (⇒-intro
            (∨-elim {Γ = Γ , ψ}
              (∨-intro₁ (ψ ∧ ω) (assume {Γ = Γ , ψ} φ))
              (∨-intro₂ φ
                (∧-intro
                  (weaken ω (assume {Γ = Γ} ψ))
                  (assume {Γ = Γ , ψ} ω)))))
          (∧-proj₂ (weaken ψ seq)))))
    (∧-proj₁ seq)

∨-morgan₁ {Γ}{φ}{ψ} =
  ⇒-elim $
    ⇒-intro $
      ∧-intro
        (¬-intro $
          ¬-elim
            (weaken φ $
              assume {Γ = Γ} (¬ (φ ∨ ψ)))
            (∨-intro₁ ψ $
              assume {Γ = Γ , ¬ (φ ∨ ψ)} φ))
        (¬-intro $
          ¬-elim
            (weaken ψ $
              assume {Γ = Γ} (¬ (φ ∨ ψ)))
            (∨-intro₂ φ $
              assume {Γ = Γ , ¬ (φ ∨ ψ)} ψ))

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
