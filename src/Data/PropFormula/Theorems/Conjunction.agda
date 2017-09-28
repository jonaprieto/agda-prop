------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ∧ connective.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.PropFormula.Theorems.Conjunction ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Syntax n
open import Data.PropFormula.Theorems.Classical n

open import Function using ( _$_ ; _∘_  )

------------------------------------------------------------------------------

∧-assoc
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ∧ (ψ ∧ γ)
  → Γ ⊢ (φ ∧ ψ) ∧ γ

∧-comm
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ∧ ψ
  → Γ ⊢ ψ ∧ φ

∧-dist₁
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ∧ (ψ ∨ γ)
  → Γ ⊢ (φ ∧ ψ) ∨ (φ ∧ γ)

∧-dist₂
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ∧ ψ) ∨ (φ ∧ γ)
  → Γ ⊢ φ ∧ (ψ ∨ γ)

∧-dist
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ∧ (ψ ∨ γ) ⇔ (φ ∧ ψ) ∨ (φ ∧ γ)

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
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ⇒ γ
  → Γ ⊢ φ ∧ ψ
  → Γ ⊢ γ ∧ ψ

subst⊢∧₂
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ ψ ⇒ γ
  → Γ ⊢ φ ∧ ψ
  → Γ ⊢ φ ∧ γ

-- A basic one.

¬∧-to-⊥
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ φ ∧ φ
  → Γ ⊢ ⊥

------------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------------

∧-assoc Γ⊢φ∧ψ∧γ =
  ∧-intro
    (∧-intro
      (∧-proj₁  Γ⊢φ∧ψ∧γ)
      ((∧-proj₁ ∘ ∧-proj₂) Γ⊢φ∧ψ∧γ))
    ((∧-proj₂ ∘ ∧-proj₂) Γ⊢φ∧ψ∧γ)

∧-comm Γ⊢φ∧ψ =
  ∧-intro
    (∧-proj₂ Γ⊢φ∧ψ)
    (∧-proj₁ Γ⊢φ∧ψ)

∧-dist₁ {Γ}{φ}{ψ}{γ} Γ⊢φ∧ψ∨γ =
  ⇒-elim
    (⇒-intro $
      ∨-elim {Γ = Γ}
        (∨-intro₁ (φ ∧ γ)
          (∧-intro
            (weaken ψ (∧-proj₁ Γ⊢φ∧ψ∨γ))
            (assume {Γ = Γ} ψ)))
        (∨-intro₂ (φ ∧ ψ)
          (∧-intro
            (weaken γ  (∧-proj₁ Γ⊢φ∧ψ∨γ))
            (assume {Γ = Γ} γ))))
    (∧-proj₂ Γ⊢φ∧ψ∨γ)

∧-dist₂ {Γ}{φ}{ψ}{γ} =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∧-intro
          (∧-proj₁
            (assume {Γ = Γ} (φ ∧ ψ)))
          (∨-intro₁ γ
            (∧-proj₂
              (assume {Γ = Γ} (φ ∧ ψ)))))
        (∧-intro
          (∧-proj₁
            (assume {Γ = Γ} (φ ∧ γ)))
          (∨-intro₂ ψ
            (∧-proj₂
              (assume {Γ = Γ} (φ ∧ γ)))))))

∧-dist {Γ}{φ}{ψ}{γ} =
  ⇔-intro
    (∧-dist₁ (assume {Γ = Γ} (φ ∧ (ψ ∨ γ))))
    (∧-dist₂ (assume {Γ = Γ} (φ ∧ ψ ∨ (φ ∧ γ))))

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

¬∧-to-⊥ {Γ}{φ} Γ⊢φ = ¬-elim (∧-proj₁ Γ⊢φ) (∧-proj₂ Γ⊢φ)
