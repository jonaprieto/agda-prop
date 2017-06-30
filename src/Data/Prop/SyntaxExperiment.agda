------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Syntax Experiment definitions.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.SyntaxExperiment ( n : ℕ ) where

open import Data.Prop.Syntax n
open import Data.Prop.Views n

open import Data.List public
open import Relation.Binary.PropositionalEquality using (_≡_)

data _⊢∧_ : Ctxt → List Prop → Set where

  top-intro : ∀ {Γ}
            → Γ ⊢∧ []

  thm-intro : ∀ {Γ} {φ}
            → Γ ⊢ φ
            → Γ ⊢∧ [ φ ]

  ∧-intro   : ∀ {Γ} {φ} {L}
            → Γ ⊢ φ
            → Γ ⊢∧ L
            → Γ ⊢∧ (φ ∷ L)

lemma-++
  : ∀ {Γ} {L₁ L₂}
  → Γ ⊢∧ L₁ → Γ ⊢∧ L₂
  → Γ ⊢∧ (L₁ ++ L₂)
lemma-++ top-intro Γ⊢∧L₁        = Γ⊢∧L₁
lemma-++ (thm-intro x) Γ⊢∧L₁    = ∧-intro x Γ⊢∧L₁
lemma-++ (∧-intro x thm1) Γ⊢∧L₁ = ∧-intro x (lemma-++ thm1 Γ⊢∧L₁)

toList : Prop → List Prop
toList φ with conj-view φ
toList .(φ₁ ∧ φ₂) | conj φ₁ φ₂ = toList φ₁ ++ toList φ₂
toList φ          | other .φ   = [ φ ]

⊢-to-⊢∧
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢∧ toList φ

⊢-to-⊢∧ {Γ} {φ} Γ⊢φ with conj-view φ
... | conj φ₁ φ₂ = lemma-++ (⊢-to-⊢∧ (∧-proj₁ Γ⊢φ)) (⊢-to-⊢∧ (∧-proj₂ Γ⊢φ))
... | other .φ   = thm-intro Γ⊢φ

∧-proj
  : ∀ {Γ} {φ} {L}
  → Γ ⊢∧ (φ ∷ L)
  → Γ ⊢ φ

∧-proj {Γ} {φ} {.[]} (thm-intro Γ⊢φ)   = Γ⊢φ
∧-proj {Γ} {φ} {L}   (∧-intro Γ⊢φ thm) = Γ⊢φ

to-∧ : List Prop → Prop
to-∧ []       = ⊤
to-∧ (φ ∷ []) = φ
to-∧ (φ ∷ L)  = φ ∧ (to-∧ L)

⊢∧-to-⊢
  : ∀ {Γ} {L}
  → Γ ⊢∧ L
  → Γ ⊢ to-∧ L
⊢∧-to-⊢ {Γ} {[]}         _                 = ⊤-intro
⊢∧-to-⊢ {Γ} {x ∷ []}     Γ⊢∧L              = ∧-proj Γ⊢∧L
⊢∧-to-⊢ {Γ} {x ∷ x₁ ∷ L} (∧-intro x₂ Γ⊢∧L) = ∧-intro x₂ (⊢∧-to-⊢ Γ⊢∧L)

-- Bag Equivalance

