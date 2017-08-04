------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ⇔ connective.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.Theorems.Biimplication ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Theorems.Classical n
open import Data.Prop.Theorems.Implication n
  using ( ⇒-to-¬∨; ⇒⇒-to-∧⇒; ∧⇒-to-⇒⇒ )
open import Data.Prop.Theorems.Negation n
  using ( ¬-equiv₁ ; ¬-equiv₂; ¬∨-to-⇒; ¬¬-equiv₁; ¬¬-equiv₂ )
open import Data.Prop.Syntax n

open import Function using ( _$_ )

------------------------------------------------------------------------------

⇔-equiv₁
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ⇔ ψ
  → Γ ⊢ (φ ⇒ ψ) ∧ (ψ ⇒ φ)

⇔-equiv₂
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ (φ ⇒ ψ) ∧ (ψ ⇒ φ)
  → Γ ⊢ φ ⇔ ψ

⇔-equiv
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ (φ ⇔ ψ) ⇔ ((φ ⇒ ψ) ∧ (ψ ⇒ φ))

postulate
  ⇔-assoc₁
    : ∀ {Γ} {φ ψ γ}
    → Γ ⊢ φ ⇔ (ψ ⇔ γ)
    → Γ ⊢ (φ ⇔ ψ) ⇔ γ

  ⇔-assoc₂
    : ∀ {Γ} {φ ψ γ}
    → Γ ⊢ (φ ⇔ ψ) ⇔ γ
    → Γ ⊢ φ ⇔ (ψ ⇔ γ)

⇔-assoc
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ⇔ (ψ ⇔ γ)) ⇔ ((φ ⇔ ψ) ⇔ γ)

⇔-comm
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ⇔ ψ
  → Γ ⊢ ψ ⇔ φ

⇒-⇔-¬∨
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ (φ ⇒ ψ) ⇔ (¬ φ ∨ ψ)

thm-bicon₀
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ⇔ ψ → Γ ⊢ ¬ φ
  → Γ ⊢ ¬ ψ
⇔-¬-to-¬ = thm-bicon₀

thm-bicon₁
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ φ ⇔ ψ → Γ ⊢ φ
  → Γ ⊢ ¬ ψ
¬⇔-to-¬ = thm-bicon₁

¬-equiv
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ φ ⇔ (φ ⇒ ⊥)

¬¬-equiv
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ (¬ φ) ⇔ φ

⇒⇒-⇔-∧⇒
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ⇒ (ψ ⇒ γ)) ⇔ ((φ ∧ ψ) ⇒ γ)

⇔-trans
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ γ ⇔ φ
  → Γ ⊢ φ ⇔ ψ
  → Γ ⊢ γ ⇔ ψ
subst⊢⇔₁ = ⇔-trans

------------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------------

⇔-equiv₁ {Γ}{φ}{ψ} Γ⊢φ⇔ψ =
  ∧-intro
    (⇒-intro
      (⇔-elim₁
        (assume {Γ = Γ} φ)
        (weaken φ Γ⊢φ⇔ψ)))
    (⇒-intro
      (⇔-elim₂
        (assume {Γ = Γ} ψ)
         (weaken ψ Γ⊢φ⇔ψ)))

⇔-equiv₂ {Γ}{φ}{ψ} Γ⊢⟪φ⇒ψ⟫∧⟪ψ⇒φ⟫ =
  ⇔-intro
    (⇒-elim
      (weaken φ (∧-proj₁ Γ⊢⟪φ⇒ψ⟫∧⟪ψ⇒φ⟫))
      (assume {Γ = Γ} φ))
    (⇒-elim
      (weaken ψ (∧-proj₂ Γ⊢⟪φ⇒ψ⟫∧⟪ψ⇒φ⟫))
      (assume {Γ = Γ} ψ))

⇔-equiv {Γ}{φ}{ψ} =
  ⇔-intro
    (⇔-equiv₁
      (assume {Γ = Γ} (φ ⇔ ψ)))
    (⇔-equiv₂
      (assume {Γ = Γ} ((φ ⇒ ψ) ∧ (ψ ⇒ φ))))

⇔-assoc {Γ}{φ}{ψ}{γ} =
  ⇔-intro
    (⇔-assoc₁ (assume {Γ = Γ} (φ ⇔ ψ ⇔ γ)))
    (⇔-assoc₂ (assume {Γ = Γ} ((φ ⇔ ψ) ⇔ γ)))

⇔-comm {Γ}{φ}{ψ} Γ⊢φ⇔ψ =
  ⇔-intro
    (⇔-elim₂ (assume {Γ = Γ} ψ) (weaken ψ Γ⊢φ⇔ψ))
    (⇔-elim₁ (assume {Γ = Γ} φ) (weaken φ Γ⊢φ⇔ψ))

⇒-⇔-¬∨ {Γ}{φ}{ψ} =
  ⇔-intro
    (⇒-to-¬∨ (assume {Γ = Γ} (φ ⇒ ψ)))
    (¬∨-to-⇒ (assume {Γ = Γ} (¬ φ ∨ ψ)))

thm-bicon₀ {Γ}{φ}{ψ} Γ⊢φ⇔ψ Γ⊢¬ψ =
  ¬-equiv₂
    (⇒-intro
      (¬-elim
        (weaken ψ Γ⊢¬ψ)
      (⇔-elim₂
        (assume {Γ = Γ} ψ)
        (weaken ψ Γ⊢φ⇔ψ))))

thm-bicon₁ {Γ}{φ}{ψ} Γ⊢¬φ⇔ψ Γ⊢φ =
  ¬-equiv₂
    (⇒-intro
      (¬-elim
        (⇔-elim₂
          (assume {Γ = Γ} ψ)
          (weaken ψ Γ⊢¬φ⇔ψ))
        (weaken ψ Γ⊢φ)))

¬-equiv {Γ}{φ} =
  ⇔-intro
    (¬-equiv₁ (assume {Γ = Γ} (¬ φ)))
    (¬-equiv₂ (assume {Γ = Γ} (φ ⇒ ⊥)))

¬¬-equiv {Γ}{φ} =
  ⇔-intro
    (¬¬-equiv₁ (assume {Γ = Γ} (¬ (¬ φ))))
    (¬¬-equiv₂ (assume {Γ = Γ} φ))

⇒⇒-⇔-∧⇒ {Γ}{φ}{ψ}{γ} =
  ⇔-intro
    (⇒⇒-to-∧⇒ (assume {Γ = Γ} (φ ⇒ ψ ⇒ γ)))
    (∧⇒-to-⇒⇒ (assume {Γ = Γ} (φ ∧ ψ ⇒ γ)))

⇔-trans {Γ}{φ}{ψ}{γ} Γ⊢γ⇔φ Γ⊢φ⇔ψ =
  ⇔-intro
    (⇔-elim₁
      (⇔-elim₁
        (assume {Γ = Γ} γ)
        (weaken γ Γ⊢γ⇔φ))
      (weaken γ Γ⊢φ⇔ψ))
    (⇔-elim₂
      (⇔-elim₂
        (assume {Γ = Γ} ψ)
        (weaken ψ Γ⊢φ⇔ψ))
      (weaken ψ Γ⊢γ⇔φ))
