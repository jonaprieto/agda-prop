------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ¬ connective.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.Theorems.Negation ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Properties n
  using ( ¬-injective ; subst )
open import Data.Prop.Syntax n

open import Function                              using ( _$_ ; _∘_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym )

------------------------------------------------------------------------------

¬-equiv
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ φ
  → Γ ⊢ φ ⇒ ⊥
¬-to-⇒⊥ = ¬-equiv

¬¬-equiv
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ (¬ φ)
  → Γ ⊢ φ

¬-equiv₂
  : ∀ {Γ} {φ}
  → Γ ⊢ φ ⇒ ⊥
  → Γ ⊢ ¬ φ
⇒⊥-to-¬ = ¬-equiv₂

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

------------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------------

¬-equiv {Γ}{φ} Γ⊢¬φ =
  ⇒-intro
    (¬-elim
      (weaken φ Γ⊢¬φ)
      (assume {Γ = Γ} φ))

¬-equiv₂ {Γ}{φ} Γ⊢φ⇒⊥ =
  ¬-intro
    (⇒-elim
      (weaken φ Γ⊢φ⇒⊥)
      (assume {Γ = Γ} φ))

¬¬-equiv {Γ}{φ} Γ⊢¬¬φ =
  (⇒-elim
    (⇒-intro $ RAA
      (¬-elim
        (weaken (¬ φ) $
          assume {Γ = Γ} $ ¬ (¬ φ))
        (assume {Γ = Γ , ¬ (¬ φ)} $ ¬ φ)))
    Γ⊢¬¬φ)

¬⊤-to-⊥ Γ⊢¬⊤ = ¬-elim Γ⊢¬⊤ ⊤-intro

¬⊥-to-⊤ Γ⊢¬⊥ = ⊤-intro

⊤-to-¬⊥ {Γ} = λ _ → ¬-intro (assume {Γ = Γ} ⊥)

⊥-to-¬⊤ = ¬-intro ∘ weaken ⊤

¬-inside {Γ}{φ}{ψ} φ≡ψ Γ⊢¬φ =
  ¬-equiv₂
    (⇒-intro
      (⇒-elim
        (¬-equiv
          (weaken ψ Γ⊢¬φ))
        (subst
          (sym φ≡ψ)
          (assume {Γ = Γ} ψ))))
