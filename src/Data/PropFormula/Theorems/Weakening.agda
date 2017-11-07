------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Extension Theorems of the Syntax definitions.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.PropFormula.Theorems.Weakening ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Syntax n
open import Data.PropFormula.Properties n using ( substΓ )

open import Data.List using ( List ; [] ; _∷_ ; _++_ ; [_] )

open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; cong; trans; sym)

------------------------------------------------------------------------------

-- Theorem.
weaken-Δ₁
  : ∀ {Γ} {φ}
  → (Δ : Ctxt)
  → Γ ⊢ φ
  → Γ ⨆ Δ ⊢ φ

-- Proof.
weaken-Δ₁ {[]} {φ} [] Γ⊢φ = Γ⊢φ
weaken-Δ₁ {x ∷ Γ} {φ} [] Γ⊢φ  = substΓ (sym helper) Γ⊢φ
  where
    helper : ∀ {Γ} → Γ ⨆ [] ≡ Γ
    helper {[]}    = refl
    helper {x ∷ Γ} rewrite helper {Γ = Γ} = refl
weaken-Δ₁ {Γ} {φ} (x ∷ []) Γ⊢φ = weaken x Γ⊢φ
weaken-Δ₁ {Γ} {φ} (x₁ ∷ Δ) Γ⊢φ =
  substΓ
    (helper {Γ = Γ} {x = x₁})
    (weaken-Δ₁ {Γ = Γ , x₁} {φ = φ} Δ
      (weaken x₁ Γ⊢φ))
  where
    helper : ∀ {Γ Δ} {x} → (Γ , x ) ⨆  Δ ≡ Γ ⨆ (x ∷ Δ)
    helper {[]} {Δ} = refl
    helper {y ∷ Γ} {Δ} {x} rewrite helper {Γ = Γ} {Δ = Δ} {x = x} = refl
-------------------------------------------------------------------------- ■

-- Theorem.
weaken-Δ₂
  :  ∀ {Γ} {φ}
  → (Δ : Ctxt)
  → Γ ⊢ φ
  → Δ ⨆ Γ ⊢ φ

-- Proof.
weaken-Δ₂ {Γ}  {φ} []           Γ⊢φ = Γ⊢φ
weaken-Δ₂ {[]} {φ} (hyp ∷ [])   Γ⊢φ = weaken₂ hyp Γ⊢φ
weaken-Δ₂ {Γ}  {φ} (hyp ∷ [])   Γ⊢φ = weaken₂ hyp Γ⊢φ
weaken-Δ₂ {Γ}  {φ} (hyp ∷ hyps) Γ⊢φ = weaken₂ hyp (weaken-Δ₂ hyps Γ⊢φ)
-------------------------------------------------------------------------- ■
