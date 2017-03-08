
open import Data.Prop 2

⋀comm : ∀ {Γ}{φ ψ : Prop} → Γ ⊢ φ ∧ ψ ⇒ ψ ∧ φ
⋀comm {Γ} {φ = φ}{ψ} =
  ⇒-intro $
    ∧-intro
      (∧-proj₂ $ assume {Γ = Γ} $ φ ∧ ψ)
      (∧-proj₁ {ψ = ψ} $ assume {Γ = Γ} $ φ ∧ ψ)
