------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ∧ connective.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module Data.Prop.Theorems.Conjunction (n : ℕ) where

open import Data.Prop.Syntax n
open import Function using ( _$_ ; _∘_  )


∧-assoc : ∀ {Γ} {φ ψ ω}
        → Γ ⊢ φ ∧ (ψ ∧ ω)
        → Γ ⊢ (φ ∧ ψ) ∧ ω


∧-comm : ∀ {Γ} {φ ψ}
       → Γ ⊢ φ ∧ ψ
       → Γ ⊢ ψ ∧ φ


∧-dist₁ : ∀ {Γ} {φ ψ ω}
        → Γ ⊢ φ ∧ (ψ ∨ ω)
        → Γ ⊢ (φ ∧ ψ) ∨ (φ ∧ ω)


∧-dist₂ : ∀ {Γ} {φ ψ ω}
         → Γ ⊢ (φ ∧ ψ) ∨ (φ ∧ ω)
         → Γ ⊢ φ ∧ (ψ ∨ ω)


∧-morgan₁ : ∀ {Γ} {φ ψ}
          → Γ ⊢ ¬ (φ ∧ ψ)
          → Γ ⊢ ¬ φ ∨ ¬ ψ


∧-morgan₂ : ∀ {Γ} {φ ψ}
          → Γ ⊢ ¬ φ ∨ ¬ ψ
          → Γ ⊢ ¬ (φ ∧ ψ)


------------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------------


∧-assoc {Γ}{φ}{ψ}{ω} seq =
  ∧-intro
    (∧-intro
      (∧-proj₁  seq)
      ((∧-proj₁ ∘ ∧-proj₂) seq))
    ((∧-proj₂ ∘ ∧-proj₂) seq)


∧-comm {Γ}{φ}{ψ} seq =
  ∧-intro
    (∧-proj₂ seq)
    (∧-proj₁ seq)


∧-dist₁ {Γ}{φ}{ψ}{ω} seq =
  ⇒-elim (
    ⇒-intro $
      ∨-elim {Γ = Γ}
        (∨-intro₁ (φ ∧ ω)
          (∧-intro
            (weaken ψ (∧-proj₁ seq))
            (assume {Γ = Γ} ψ)
            ))
        (∨-intro₂ (φ ∧ ψ)
          (∧-intro
            (weaken ω  (∧-proj₁ seq))
            (assume {Γ = Γ} ω)))
      )
    (∧-proj₂ seq)


∧-dist₂ {Γ}{φ}{ψ}{ω} seq =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∧-intro
          (∧-proj₁
            (assume {Γ = Γ} (φ ∧ ψ)))
          (∨-intro₁ ω
            (∧-proj₂
              (assume {Γ = Γ} (φ ∧ ψ)))))
        (∧-intro
          (∧-proj₁
            (assume {Γ = Γ} (φ ∧ ω)))
          (∨-intro₂ ψ
            (∧-proj₂
              (assume {Γ = Γ} (φ ∧ ω)))))))
    seq

--- De Morgan's Law

∧-morgan₁ {Γ}{φ}{ψ} =
  ⇒-elim $
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


∧-morgan₂ {Γ}{φ}{ψ} =
  ⇒-elim $
    ⇒-intro $
      ∨-elim {Γ = Γ}
        (¬-intro $
          ¬-elim
            (weaken (φ ∧ ψ) $ assume {Γ = Γ} (¬ φ))
            (∧-proj₁ $ assume {Γ = Γ , ¬ φ} (φ ∧ ψ))
         )
        (¬-intro $
          ¬-elim
            (weaken (φ ∧ ψ) $ assume {Γ = Γ} (¬ ψ))
          (∧-proj₂ $
            assume {Γ = Γ , ¬ ψ} (φ ∧ ψ)))
