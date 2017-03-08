-- Exercises from the course Type Theory CM0859 (Prof. Andreas Abel).
-- http://www1.eafit.edu.co/asr/courses/type-theory-CM0859/exercises.pdf


open import Data.Prop 2 public

ex1 : ∀ {φ} → ∅ ⊢ φ ⇒ φ
ex1 {φ} = ⇒-intro (assume {Γ = ∅} φ)

ex2 : ∀ {φ ψ} → ∅ ⊢ (φ ∧ (φ ⇒ ψ)) ⇒ ψ
ex2 {φ} {ψ} =
  ⇒-intro
    (⇒-elim
      (∧-proj₂ (assume {Γ = ∅} (φ ∧ (φ ⇒ ψ))))
      (∧-proj₁ (assume {Γ = ∅}  (φ ∧ (φ ⇒ ψ)))))

ex3 : ∀ {φ ψ ω} → ∅ ⊢ (φ ∧ (ψ ∨ ω)) ⇒ ((φ ∧ ψ) ∨ (φ ∧ ω))
ex3 {φ} {ψ} {ω} =
  ⇒-intro
  (⇒-elim {Γ = ∅ , (φ ∧ (ψ ∨ ω))}
    (⇒-intro {Γ = ∅ , (φ ∧ (ψ ∨ ω))}
      (∨-elim {Γ = ∅ , (φ ∧ (ψ ∨ ω))}
        (∨-intro₁ {Γ = ∅ , (φ ∧ (ψ ∨ ω)) , ψ}
          (φ ∧ ω)
          (∧-intro
            (∧-proj₁ (weaken ψ (assume {Γ = ∅} (φ ∧ (ψ ∨ ω)))))
            (assume {Γ = ∅ , (φ ∧ (ψ ∨ ω)) } ψ)))
        (∨-intro₂ {Γ = ∅ , (φ ∧ (ψ ∨ ω)) , ω}
          (φ ∧ ψ)
          (∧-intro
            (∧-proj₁ (weaken ω (assume {Γ = ∅} (φ ∧ (ψ ∨ ω)))))
            (assume {Γ = ∅ , (φ ∧ (ψ ∨ ω))} ω )))))
    (∧-proj₂ (assume {Γ = ∅} (φ ∧ (ψ ∨ ω)))))
