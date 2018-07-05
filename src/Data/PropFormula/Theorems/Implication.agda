------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ⊃ connective.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.PropFormula.Theorems.Implication ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Syntax n
open import Data.PropFormula.Theorems.Classical n

open import Function using ( _$_; _∘_; flip )

------------------------------------------------------------------------------

-- Theorem.
⊃-equiv
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ⊃ ψ
  → Γ ⊢ ¬ φ ∨ ψ
⊃-to-¬∨ = ⊃-equiv

-- Proof.
⊃-equiv {φ = φ}{ψ} Γ⊢φ⊃ψ =
  (⊃-elim
    (⊃-intro
      (∨-elim
        (∨-intro₂ (¬ φ)
          (⊃-elim
            (weaken φ Γ⊢φ⊃ψ)
            (assume φ)))
        (∨-intro₁ ψ
          (assume (¬ φ)))))
      PEM)
-------------------------------------------------------------------------- ∎

-- Theorems from the book:
-- van Dalen 4th Edition. Chapter 2. Section 2.4.

-- Theorem.
vanDalen244a
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ⊃ (ψ ⊃ φ)

-- Proof.
vanDalen244a {φ = φ}{ψ} =
  (⊃-intro
    (⊃-intro
      (weaken ψ
        (assume φ))))
-------------------------------------------------------------------------- ∎

-- Theorem.
vanDalen244b
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ⊃ (¬ φ ⊃ ψ)

-- Proof.
vanDalen244b {Γ}{φ}{ψ} =
  ⊃-intro $
    ⊃-intro $
      ⊥-elim {Γ = (Γ , φ , ¬ φ)} ψ $
        ¬-elim
          (assume  {Γ = Γ , φ} (¬ φ))
          (weaken (¬ φ) (assume φ))
-------------------------------------------------------------------------- ∎

-- Theorem.
vanDalen244c
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ⊃ ψ) ⊃ ((ψ ⊃ γ) ⊃ (φ ⊃ γ))

-- Proof.
vanDalen244c {Γ}{φ}{ψ}{γ} =
  ⊃-intro $
    ⊃-intro $
      ⊃-intro $
        ⊃-elim
          (weaken φ $
            assume {Γ = Γ , φ ⊃ ψ} $ ψ ⊃ γ)
          (⊃-elim
            (weaken φ $
              weaken (ψ ⊃ γ) $
                assume $ φ ⊃ ψ)
            (assume {Γ = Γ , φ ⊃ ψ , ψ ⊃ γ} φ))
-------------------------------------------------------------------------- ∎

-- Theorem.
vanDalen244d
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ ψ ⊃ ¬ φ
  → Γ ⊢ φ ⊃ ψ
¬⊃¬-to-⊃ = vanDalen244d
contraposition₁ = vanDalen244d

-- Proof.
vanDalen244d {Γ}{φ}{ψ} Γ⊢¬ψ⊃¬φ =
  (⊃-elim
    (⊃-intro $
      (⊃-intro $
        RAA $
          ¬-elim
            (⊃-elim
              (weaken (¬ ψ) $
                weaken φ $
                  assume $ ¬ ψ  ⊃ ¬ φ)
              (assume {Γ = Γ , ¬ ψ ⊃ ¬ φ , φ} $ ¬ ψ))
            (weaken (¬ ψ) $
              assume {Γ = Γ , ¬ ψ ⊃ ¬ φ} φ)))
      Γ⊢¬ψ⊃¬φ)
-------------------------------------------------------------------------- ∎

-- Theorem.
contraposition₂
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ⊃ ψ
  → Γ ⊢ ¬ ψ ⊃ ¬ φ
⊃-to-¬⊃¬ = contraposition₂

-- Proof.
contraposition₂ {Γ}{φ}{ψ} Γ⊢φ⊃ψ =
  ⊃-intro
    (¬-intro
      (¬-elim
        (weaken φ (assume (¬ ψ)))
        (⊃-elim
          (weaken φ (weaken (¬ ψ) Γ⊢φ⊃ψ))
          (assume {Γ = Γ , ¬ ψ} φ))))
-------------------------------------------------------------------------- ∎

-- Theorem.
vanDalen244e
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ (¬ φ) ⊃ φ

-- Proof.
vanDalen244e {Γ}{φ} =
  ⊃-intro $ RAA
    (¬-elim
      (weaken (¬ φ) $
        assume $ ¬ (¬ φ))
      (assume {Γ = Γ , ¬ (¬ φ)} $ ¬ φ))
-------------------------------------------------------------------------- ∎

-- Theorem.
⊃⊃-to-∧⊃
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ⊃ (ψ ⊃ γ)
  → Γ ⊢ (φ ∧ ψ) ⊃ γ

-- Proof.
⊃⊃-to-∧⊃ {Γ}{φ}{ψ} Γ⊢φ⊃ψ⊃γ =
  ⊃-intro
    (⊃-elim
      (⊃-elim
        (weaken (φ ∧ ψ) Γ⊢φ⊃ψ⊃γ)
        (∧-proj₁ (assume (φ ∧ ψ))))
      (∧-proj₂ (assume (φ ∧ ψ))))
-------------------------------------------------------------------------- ∎

-- Theorem.
∧⊃-to-⊃⊃
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ∧ ψ) ⊃ γ
  → Γ ⊢ φ ⊃ (ψ ⊃ γ)

-- Proof.
∧⊃-to-⊃⊃ {Γ}{φ}{ψ} Γ⊢φ∧ψ⊃γ =
  ⊃-intro
    (⊃-intro
      (⊃-elim
        (weaken ψ (weaken φ Γ⊢φ∧ψ⊃γ))
        (∧-intro
          (weaken ψ (assume φ))
          (assume {Γ = Γ , φ} ψ))))
-------------------------------------------------------------------------- ∎

-- Theorem.
⊃∧⊃-to-⊃∧
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ⊃ ψ) ∧ (φ ⊃ γ)
  → Γ ⊢ φ ⊃ (ψ ∧ γ)

-- Proof.
⊃∧⊃-to-⊃∧ {φ = φ} Γ⊢⟨φ⊃ψ⟩∧⟨φ⊃γ⟩ =
  ⊃-intro
    (∧-intro
      (⊃-elim (∧-proj₁ (weaken φ Γ⊢⟨φ⊃ψ⟩∧⟨φ⊃γ⟩)) (assume φ))
      (⊃-elim (∧-proj₂ (weaken φ Γ⊢⟨φ⊃ψ⟩∧⟨φ⊃γ⟩)) (assume φ)))
-------------------------------------------------------------------------- ∎

-- Theorem.
subst⊢⊃₁
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ γ ⊃ φ
  → Γ ⊢ φ ⊃ ψ
  → Γ ⊢ γ ⊃ ψ

-- Proof.
subst⊢⊃₁ {γ = γ} Γ⊢ψ⊃γ Γ⊢φ⊃ψ =
  ⊃-intro
    (⊃-elim
      (weaken γ Γ⊢φ⊃ψ)
      (⊃-elim (weaken γ Γ⊢ψ⊃γ) (assume γ)))
-------------------------------------------------------------------------- ∎

-- Theorem.
subst⊢⊃₂
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ ψ ⊃ γ
  → Γ ⊢ φ ⊃ ψ
  → Γ ⊢ φ ⊃ γ

-- Proof.
subst⊢⊃₂ {φ = φ} Γ⊢γ⊃φ Γ⊢φ⊃ψ =
 ⊃-intro
   (⊃-elim
     (weaken φ Γ⊢γ⊃φ)
     (⊃-elim (weaken φ Γ⊢φ⊃ψ) (assume φ)))
-------------------------------------------------------------------------- ∎

-- Theorem.
⊃-trans
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ⊃ ψ
  → Γ ⊢ ψ ⊃ γ
  → Γ ⊢ φ ⊃ γ

-- Proof.
⊃-trans Γ⊢φ⊃ψ Γ⊢ψ⊃γ = subst⊢⊃₂ Γ⊢ψ⊃γ Γ⊢φ⊃ψ
-------------------------------------------------------------------------- ∎
