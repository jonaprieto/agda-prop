------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ¬ connective.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.PropFormula.Theorems.Negation ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Properties n using ( ¬-injective ; subst )
open import Data.PropFormula.Syntax n
open import Data.PropFormula.Theorems.Classical n
open import Data.PropFormula.Theorems.Implication n using ( subst⊢⊃₁ )

open import Function using ( _$_ ; _∘_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym )

------------------------------------------------------------------------------

-- Theorem.
¬-equiv₁
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ φ
  → Γ ⊢ φ ⊃ ⊥
¬-to-⊃⊥ = ¬-equiv₁

-- Proof.
¬-equiv₁ {φ = φ} Γ⊢¬φ =
  ⊃-intro
    (¬-elim
      (weaken φ Γ⊢¬φ)
      (assume φ))
-------------------------------------------------------------------------- ∎

-- Theorem.
¬-equiv₂
  : ∀ {Γ} {φ}
  → Γ ⊢ φ ⊃ ⊥
  → Γ ⊢ ¬ φ
⊃⊥-to-¬ = ¬-equiv₂

-- Proof.
¬-equiv₂ {φ = φ} Γ⊢φ⊃⊥ =
  ¬-intro
    (⊃-elim
      (weaken φ Γ⊢φ⊃⊥)
      (assume φ))
-------------------------------------------------------------------------- ∎

-- Theorem.
¬¬-equiv₁
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ (¬ φ)
  → Γ ⊢ φ

-- Proof.
¬¬-equiv₁ {Γ}{φ} Γ⊢¬¬φ =
  (⊃-elim
    (⊃-intro $ RAA
      (¬-elim
        (weaken (¬ φ) $
          assume $ ¬ (¬ φ))
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
  ⊃⊥-to-¬
    (⊃-intro
      (¬-elim
        (assume (¬ φ))
        (weaken (¬ φ) Γ⊢φ)))
-------------------------------------------------------------------------- ∎

-- Theorem.
¬∨-to-⊃
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ φ ∨ ψ
  → Γ ⊢ φ ⊃ ψ

-- Proof.
¬∨-to-⊃ {Γ}{φ}{ψ} =
  ⊃-elim $
    ⊃-intro $
      ∨-elim
        (⊃-intro $
          ⊥-elim {Γ = Γ , ¬ φ , φ} ψ
          (¬-elim
            (weaken φ $
              assume (¬ φ))
            (assume {Γ = Γ , ¬ φ} φ)))
        (⊃-intro $
          weaken φ $
            assume ψ)
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
⊤-to-¬⊥ = λ _ → ¬-intro (assume ⊥)
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
¬-inside {φ = φ}{ψ} φ≡ψ Γ⊢¬φ =
  ¬-equiv₂
    (⊃-intro
      (⊃-elim
        (¬-equiv₁
          (weaken ψ Γ⊢¬φ))
        (subst
          (sym φ≡ψ)
          (assume ψ))))
-------------------------------------------------------------------------- ∎

-- Theorem.
subst⊢¬
  : ∀ {Γ} {φ γ}
  → Γ ⊢ γ ⊃ φ
  → Γ ⊢ ¬ φ
  → Γ ⊢ ¬ γ

-- Proof.
subst⊢¬ Γ⊢γ⊃φ Γ⊢¬φ = ⊃⊥-to-¬ (subst⊢⊃₁ Γ⊢γ⊃φ (¬-to-⊃⊥ Γ⊢¬φ))
-------------------------------------------------------------------------- ∎

-- Theorem.
¬⇔-to-⊃¬∧⊃¬
  : ∀ {Γ} {φ₁ φ₂}
  → Γ ⊢ ¬ (φ₁ ⇔ φ₂)
  → Γ ⊢ (φ₁ ⊃ ¬ φ₂) ∧ (φ₂ ⊃ ¬ φ₁)

-- Proof.
¬⇔-to-⊃¬∧⊃¬ {Γ}{φ₁}{φ₂} thm =
  ∧-intro
    (⊃-intro
      (¬-intro
        (¬-elim
          (weaken φ₂ $ weaken φ₁ thm)
          (⇔-intro
            (weaken φ₁ $ assume {Γ = Γ , φ₁} φ₂)
            (weaken φ₂ $ weaken φ₂ $ assume φ₁)))))
    (⊃-intro
      (¬-intro
        (¬-elim (weaken φ₁ $ weaken φ₂ thm)
          (⇔-intro
            (weaken φ₁ $ weaken φ₁ $ assume φ₂)
            (weaken φ₂ $ assume {Γ = Γ , φ₂} φ₁)))))
-------------------------------------------------------------------------- ∎
