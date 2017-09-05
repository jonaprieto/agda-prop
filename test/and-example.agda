open import Data.PropFormula 2

⋀comm : ∀ {Γ}{φ ψ : PropFormula} → Γ ⊢ φ ∧ ψ ⇒ ψ ∧ φ
⋀comm {Γ} {φ = φ}{ψ} =
  ⇒-intro $
    ∧-intro
      (∧-proj₂ $ assume {Γ = Γ} $ φ ∧ ψ)
      (∧-proj₁ {ψ = ψ} $ assume {Γ = Γ} $ φ ∧ ψ)
