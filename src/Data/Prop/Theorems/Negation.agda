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

¬-equiv : ∀ {Γ} {φ}
        → Γ ⊢ ¬ φ
        → Γ ⊢ φ ⇒ ⊥


¬-equiv₂ : ∀ {Γ} {φ}
           → Γ ⊢ φ ⇒ ⊥
           → Γ ⊢ ¬ φ


¬-⊤  : ∀ {Γ}
     → Γ ⊢ ¬ ⊤
     → Γ ⊢ ⊥


¬-⊤₂ : ∀ {Γ}
     → Γ ⊢ ⊤
     → Γ ⊢ ¬ ⊥


¬-⊥₁ : ∀ {Γ}
     → Γ ⊢ ¬ ⊥
     → Γ ⊢ ⊤


¬-⊥₂ : ∀ {Γ}
     → Γ ⊢ ⊥
     → Γ ⊢ ¬ ⊤


or-to-impl : ∀ {Γ} {φ ψ}
           → Γ ⊢ ¬ φ ∨ ψ
           → Γ ⊢ φ ⇒ ψ


¬-inside : ∀ {Γ} {φ ψ}
         → φ ≡ ψ
         → Γ ⊢ ¬ φ
         → Γ ⊢ ¬ ψ

------------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------------

¬-equiv {Γ}{φ} seq =
  ⇒-intro
    (¬-elim
      (weaken φ seq)
      (assume {Γ = Γ} φ))


¬-equiv₂ {Γ}{φ} seq =
  ¬-intro
    (⇒-elim
      (weaken φ seq)
      (assume {Γ = Γ} φ))


¬-⊤ seq = ¬-elim seq ⊤-intro


¬-⊤₂ {Γ} seq = ¬-intro (assume {Γ = Γ} ⊥)


¬-⊥₁ seq = ⊤-intro


¬-⊥₂ = ¬-intro ∘ weaken ⊤


or-to-impl {Γ}{φ}{ψ} =
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

¬-inside {Γ}{φ}{ψ} φ≡ψ seq =
  ¬-equiv₂
    (⇒-intro
      (⇒-elim
        (¬-equiv
          (weaken ψ seq))
        (subst
          (sym φ≡ψ)
          (assume {Γ = Γ} ψ))))
