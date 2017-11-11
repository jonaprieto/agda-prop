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


-- Theorem.
¬-equiv₁
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ φ
  → Γ ⊢ φ ⇒ ⊥
¬-to-⇒⊥ = ¬-equiv₁

-- Proof.
¬-equiv₁ {Γ}{φ} Γ⊢¬φ =
  ⇒-intro
    (¬-elim
      (weaken φ Γ⊢¬φ)
      (assume {Γ = Γ} φ))
-------------------------------------------------------------------------- ∎

-- Theorem.
¬-equiv₂
  : ∀ {Γ} {φ}
  → Γ ⊢ φ ⇒ ⊥
  → Γ ⊢ ¬ φ
⇒⊥-to-¬ = ¬-equiv₂

-- Proof.
¬-equiv₂ {Γ}{φ} Γ⊢φ⇒⊥ =
  ¬-intro
    (⇒-elim
      (weaken φ Γ⊢φ⇒⊥)
      (assume {Γ = Γ} φ))
-------------------------------------------------------------------------- ∎

-- Theorem.
¬¬-equiv₁
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ (¬ φ)
  → Γ ⊢ φ

-- Proof.
¬¬-equiv₁ {Γ}{φ} Γ⊢¬¬φ =
  (⇒-elim
    (⇒-intro $ RAA
      (¬-elim
        (weaken (¬ φ) $
          assume {Γ = Γ} $ ¬ (¬ φ))
        (assume {Γ = Γ , ¬ (¬ φ)} $ ¬ φ)))
    Γ⊢¬¬φ)
-------------------------------------------------------------------------- ∎

-- Theorem.
¬¬-equiv₂
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ ¬ (¬ φ)

-- Proof.
¬¬-equiv₂ {Γ}{φ} Γ⊢φ =
  ⇒⊥-to-¬
    (⇒-intro
      (¬-elim
        (assume {Γ = Γ} (¬ φ))
        (weaken (¬ φ) Γ⊢φ)))
-------------------------------------------------------------------------- ∎

-- Theorem.
¬∨-to-⇒
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ φ ∨ ψ
  → Γ ⊢ φ ⇒ ψ

-- Proof.
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
-------------------------------------------------------------------------- ∎

-- Theorem.
¬⊤-to-⊥
  : ∀ {Γ}
  → Γ ⊢ ¬ ⊤
  → Γ ⊢ ⊥

-- Proof.
¬⊤-to-⊥ Γ⊢¬⊤ = ¬-elim Γ⊢¬⊤ ⊤-intro
-------------------------------------------------------------------------- ∎

-- Theorem.
⊤-to-¬⊥
  : ∀ {Γ}
  → Γ ⊢ ⊤
  → Γ ⊢ ¬ ⊥

-- Proof.
⊤-to-¬⊥ {Γ} = λ _ → ¬-intro (assume {Γ = Γ} ⊥)
-------------------------------------------------------------------------- ∎

-- Theorem.
¬⊥-to-⊤
  : ∀ {Γ}
  → Γ ⊢ ¬ ⊥
  → Γ ⊢ ⊤

-- Proof.
¬⊥-to-⊤ Γ⊢¬⊥ = ⊤-intro
-------------------------------------------------------------------------- ∎

-- Theorem.
⊥-to-¬⊤
  : ∀ {Γ}
  → Γ ⊢ ⊥
  → Γ ⊢ ¬ ⊤

-- Proof.
⊥-to-¬⊤ = ¬-intro ∘ weaken ⊤
-------------------------------------------------------------------------- ∎

-- Theorem.
¬-inside
  : ∀ {Γ} {φ ψ}
  → φ ≡ ψ
  → Γ ⊢ ¬ φ
  → Γ ⊢ ¬ ψ
≡-¬-to-¬ = ¬-inside

-- Proof.
¬-inside {Γ}{φ}{ψ} φ≡ψ Γ⊢¬φ =
  ¬-equiv₂
    (⇒-intro
      (⇒-elim
        (¬-equiv₁
          (weaken ψ Γ⊢¬φ))
        (subst
          (sym φ≡ψ)
          (assume {Γ = Γ} ψ))))
-------------------------------------------------------------------------- ∎

-- Theorem.
subst⊢¬
  : ∀ {Γ} {φ γ}
  → Γ ⊢ γ ⇒ φ
  → Γ ⊢ ¬ φ
  → Γ ⊢ ¬ γ

-- Proof.
subst⊢¬ {Γ}{φ}{γ} Γ⊢γ⇒φ Γ⊢¬φ =
  ⇒⊥-to-¬ (subst⊢⇒₁ Γ⊢γ⇒φ (¬-to-⇒⊥ Γ⊢¬φ))
-------------------------------------------------------------------------- ∎

-- Theorem.
¬⇔-to-⇒¬∧⇒¬
  : ∀ {Γ} {φ₁ φ₂}
  → Γ ⊢ ¬ (φ₁ ⇔ φ₂)
  → Γ ⊢ (φ₁ ⇒ ¬ φ₂) ∧ (φ₂ ⇒ ¬ φ₁)

-- Proof.
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
-------------------------------------------------------------------------- ∎
