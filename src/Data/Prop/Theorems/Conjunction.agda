------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ∧ connective.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.Theorems.Conjunction ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Data.Prop.Theorems.Classical n

open import Function using ( _$_ ; _∘_  )

------------------------------------------------------------------------------

∧-assoc
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ φ ∧ (ψ ∧ ω)
  → Γ ⊢ (φ ∧ ψ) ∧ ω

∧-comm
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ∧ ψ
  → Γ ⊢ ψ ∧ φ

∧-dist₁
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ φ ∧ (ψ ∨ ω)
  → Γ ⊢ (φ ∧ ψ) ∨ (φ ∧ ω)

∧-dist₂
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ (φ ∧ ψ) ∨ (φ ∧ ω)
  → Γ ⊢ φ ∧ (ψ ∨ ω)

∧-dist
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ φ ∧ (ψ ∨ ω) ⇔ (φ ∧ ψ) ∨ (φ ∧ ω)

∧-dmorgan₁
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ (φ ∧ ψ)
  → Γ ⊢ ¬ φ ∨ ¬ ψ
¬∧-to-¬∨¬ = ∧-dmorgan₁

∧-dmorgan₂
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ φ ∨ ¬ ψ
  → Γ ⊢ ¬ (φ ∧ ψ)
¬∨¬-to-¬∧ = ∧-dmorgan₂

∧-dmorgan
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ φ ∨ ¬ ψ ⇔ ¬ (φ ∧ ψ)
¬∨¬-⇔-¬∧ = ∧-dmorgan

subst⊢∧₁
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ φ ⇒ ω
  → Γ ⊢ φ ∧ ψ
  → Γ ⊢ ω ∧ ψ

subst⊢∧₂
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ ψ ⇒ ω
  → Γ ⊢ φ ∧ ψ
  → Γ ⊢ φ ∧ ω

------------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------------

∧-assoc Γ⊢φ∧ψ∧ω =
  ∧-intro
    (∧-intro
      (∧-proj₁  Γ⊢φ∧ψ∧ω)
      ((∧-proj₁ ∘ ∧-proj₂) Γ⊢φ∧ψ∧ω))
    ((∧-proj₂ ∘ ∧-proj₂) Γ⊢φ∧ψ∧ω)

∧-comm Γ⊢φ∧ψ =
  ∧-intro
    (∧-proj₂ Γ⊢φ∧ψ)
    (∧-proj₁ Γ⊢φ∧ψ)

∧-dist₁ {Γ}{φ}{ψ}{ω} Γ⊢φ∧ψ∨ω =
  ⇒-elim
    (⇒-intro $
      ∨-elim {Γ = Γ}
        (∨-intro₁ (φ ∧ ω)
          (∧-intro
            (weaken ψ (∧-proj₁ Γ⊢φ∧ψ∨ω))
            (assume {Γ = Γ} ψ)))
        (∨-intro₂ (φ ∧ ψ)
          (∧-intro
            (weaken ω  (∧-proj₁ Γ⊢φ∧ψ∨ω))
            (assume {Γ = Γ} ω))))
    (∧-proj₂ Γ⊢φ∧ψ∨ω)

∧-dist₂ {Γ}{φ}{ψ}{ω} =
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

∧-dist {Γ}{φ}{ψ}{ω} =
  ⇔-intro
    (∧-dist₁ (assume {Γ = Γ} (φ ∧ (ψ ∨ ω))))
    (∧-dist₂ (assume {Γ = Γ} (φ ∧ ψ ∨ (φ ∧ ω))))

∧-dmorgan₁ {Γ}{φ}{ψ} =
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

∧-dmorgan₂ {Γ}{φ}{ψ} =
  ⇒-elim $
    ⇒-intro $
      ∨-elim {Γ = Γ}
        (¬-intro $
          ¬-elim
            (weaken (φ ∧ ψ) $
              assume {Γ = Γ} (¬ φ))
            (∧-proj₁ $
              assume {Γ = Γ , ¬ φ} (φ ∧ ψ)))
        (¬-intro $
          ¬-elim
            (weaken (φ ∧ ψ) $ assume {Γ = Γ} (¬ ψ))
          (∧-proj₂ $
            assume {Γ = Γ , ¬ ψ} (φ ∧ ψ)))

∧-dmorgan {Γ}{φ}{ψ} =
  ⇔-intro
    (∧-dmorgan₂
      (assume {Γ = Γ} (¬ φ ∨ ¬ ψ)))
    (∧-dmorgan₁
      (assume {Γ = Γ} (¬ (φ ∧ ψ))))

subst⊢∧₁ {Γ}{φ}{ψ} Γ⊢φ⇒ψ Γ⊢φ∧ψ =
  ∧-intro
    (⇒-elim (∧-proj₁ (∧-intro Γ⊢φ⇒ψ Γ⊢φ∧ψ)) (∧-proj₁ Γ⊢φ∧ψ))
    (∧-proj₂ Γ⊢φ∧ψ)

subst⊢∧₂ {Γ}{φ}{ψ} Γ⊢φ⇒ψ Γ⊢φ∧ψ =
  ∧-intro
    (∧-proj₁ Γ⊢φ∧ψ)
    (⇒-elim Γ⊢φ⇒ψ (∧-proj₂ Γ⊢φ∧ψ))
