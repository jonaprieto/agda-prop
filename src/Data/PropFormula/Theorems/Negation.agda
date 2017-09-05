------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ¬ connective.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.PropFormula.Theorems.Negation ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Properties n
  using ( ¬-injective ; subst )
open import Data.PropFormula.Syntax n
open import Data.PropFormula.Theorems.Classical n
open import Data.PropFormula.Theorems.Implication n      using ( subst⊢⇒₁ )

open import Function                              using ( _$_ ; _∘_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym )

------------------------------------------------------------------------------

¬-equiv₁
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ φ
  → Γ ⊢ φ ⇒ ⊥
¬-to-⇒⊥ = ¬-equiv₁

¬-equiv₂
  : ∀ {Γ} {φ}
  → Γ ⊢ φ ⇒ ⊥
  → Γ ⊢ ¬ φ
⇒⊥-to-¬ = ¬-equiv₂

¬¬-equiv₁
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ (¬ φ)
  → Γ ⊢ φ

¬¬-equiv₂
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ ¬ (¬ φ)

¬∨-to-⇒
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ φ ∨ ψ
  → Γ ⊢ φ ⇒ ψ

¬⊤-to-⊥
  : ∀ {Γ}
  → Γ ⊢ ¬ ⊤
  → Γ ⊢ ⊥

⊤-to-¬⊥
  : ∀ {Γ}
  → Γ ⊢ ⊤
  → Γ ⊢ ¬ ⊥

¬⊥-to-⊤
  : ∀ {Γ}
  → Γ ⊢ ¬ ⊥
  → Γ ⊢ ⊤

⊥-to-¬⊤
  : ∀ {Γ}
  → Γ ⊢ ⊥
  → Γ ⊢ ¬ ⊤

¬-inside
  : ∀ {Γ} {φ ψ}
  → φ ≡ ψ
  → Γ ⊢ ¬ φ
  → Γ ⊢ ¬ ψ
≡-¬-to-¬ = ¬-inside

subst⊢¬
  : ∀ {Γ} {φ γ}
  → Γ ⊢ γ ⇒ φ
  → Γ ⊢ ¬ φ
  → Γ ⊢ ¬ γ

¬⇔-to-⇒¬∧⇒¬
  : ∀ {Γ} {φ₁ φ₂}
  → Γ ⊢ ¬ (φ₁ ⇔ φ₂)
  → Γ ⊢ (φ₁ ⇒ ¬ φ₂) ∧ (φ₂ ⇒ ¬ φ₁)

------------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------------

¬-equiv₁ {Γ}{φ} Γ⊢¬φ =
  ⇒-intro
    (¬-elim
      (weaken φ Γ⊢¬φ)
      (assume {Γ = Γ} φ))

¬-equiv₂ {Γ}{φ} Γ⊢φ⇒⊥ =
  ¬-intro
    (⇒-elim
      (weaken φ Γ⊢φ⇒⊥)
      (assume {Γ = Γ} φ))

¬¬-equiv₁ {Γ}{φ} Γ⊢¬¬φ =
  (⇒-elim
    (⇒-intro $ RAA
      (¬-elim
        (weaken (¬ φ) $
          assume {Γ = Γ} $ ¬ (¬ φ))
        (assume {Γ = Γ , ¬ (¬ φ)} $ ¬ φ)))
    Γ⊢¬¬φ)

¬¬-equiv₂ {Γ}{φ} Γ⊢φ =
  ⇒⊥-to-¬
    (⇒-intro
      (¬-elim
        (assume {Γ = Γ} (¬ φ))
        (weaken (¬ φ) Γ⊢φ)))

¬∨-to-⇒ {Γ}{φ}{ψ} =
  ⇒-elim $
    ⇒-intro $
      ∨-elim {Γ = Γ}
        (⇒-intro $
          ⊥-elim {Γ = Γ , ¬ φ , φ} ψ
          (¬-elim
            (weaken φ $
              assume {Γ = Γ} (¬ φ))
            (assume {Γ = Γ , ¬ φ} φ)))
        (⇒-intro $
          weaken φ $
            assume {Γ = Γ} ψ)

¬⊤-to-⊥ Γ⊢¬⊤ = ¬-elim Γ⊢¬⊤ ⊤-intro

¬⊥-to-⊤ Γ⊢¬⊥ = ⊤-intro

⊤-to-¬⊥ {Γ} = λ _ → ¬-intro (assume {Γ = Γ} ⊥)

⊥-to-¬⊤ = ¬-intro ∘ weaken ⊤

¬-inside {Γ}{φ}{ψ} φ≡ψ Γ⊢¬φ =
  ¬-equiv₂
    (⇒-intro
      (⇒-elim
        (¬-equiv₁
          (weaken ψ Γ⊢¬φ))
        (subst
          (sym φ≡ψ)
          (assume {Γ = Γ} ψ))))

subst⊢¬ {Γ}{φ}{γ} Γ⊢γ⇒φ Γ⊢¬φ =
  ⇒⊥-to-¬ (subst⊢⇒₁ Γ⊢γ⇒φ (¬-to-⇒⊥ Γ⊢¬φ))

¬⇔-to-⇒¬∧⇒¬ {Γ} {φ₁} {φ₂} thm =
  ∧-intro
    (⇒-intro
      (¬-intro
        (¬-elim
          (weaken φ₂ $ weaken φ₁ thm)
          (⇔-intro
            (weaken φ₁ $ assume {Γ = Γ , φ₁} φ₂)
            (weaken φ₂ $ weaken φ₂ $ assume {Γ = Γ} φ₁)))))
    (⇒-intro
      (¬-intro
        (¬-elim (weaken φ₁ $ weaken φ₂ thm)
          (⇔-intro
            (weaken φ₁ $ weaken φ₁ $ assume {Γ = Γ} φ₂)
            (weaken φ₂ $ assume {Γ = Γ , φ₂} φ₁)))))