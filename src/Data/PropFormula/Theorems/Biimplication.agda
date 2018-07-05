------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ⇔ connective.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.PropFormula.Theorems.Biimplication ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Theorems.Classical n
open import Data.PropFormula.Theorems.Implication n
  using ( ⊃-to-¬∨; ⊃⊃-to-∧⊃; ∧⊃-to-⊃⊃ )
open import Data.PropFormula.Theorems.Negation n
  using ( ¬-equiv₁ ; ¬-equiv₂; ¬∨-to-⊃; ¬¬-equiv₁; ¬¬-equiv₂ )
open import Data.PropFormula.Syntax n

open import Function using ( _$_ )

------------------------------------------------------------------------------

-- Theorem.
⇔-equiv₁
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ⇔ ψ
  → Γ ⊢ (φ ⊃ ψ) ∧ (ψ ⊃ φ)

-- Proof.
⇔-equiv₁ {Γ}{φ}{ψ} Γ⊢φ⇔ψ =
  ∧-intro
    (⊃-intro
      (⇔-elim₁
        (assume φ)
        (weaken φ Γ⊢φ⇔ψ)))
    (⊃-intro
      (⇔-elim₂
        (assume ψ)
         (weaken ψ Γ⊢φ⇔ψ)))
-------------------------------------------------------------------------- ∎

-- Theorem.
⇔-equiv₂
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ (φ ⊃ ψ) ∧ (ψ ⊃ φ)
  → Γ ⊢ φ ⇔ ψ

-- Proof.
⇔-equiv₂ {φ = φ}{ψ} Γ⊢⟪φ⊃ψ⟫∧⟪ψ⊃φ⟫ =
  ⇔-intro
    (⊃-elim
      (weaken φ (∧-proj₁ Γ⊢⟪φ⊃ψ⟫∧⟪ψ⊃φ⟫))
      (assume φ))
    (⊃-elim
      (weaken ψ (∧-proj₂ Γ⊢⟪φ⊃ψ⟫∧⟪ψ⊃φ⟫))
      (assume ψ))
-------------------------------------------------------------------------- ∎

-- Theorem.
⇔-equiv
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ (φ ⇔ ψ) ⇔ ((φ ⊃ ψ) ∧ (ψ ⊃ φ))

-- Proof.
⇔-equiv {Γ}{φ}{ψ} =
  ⇔-intro
    (⇔-equiv₁
      (assume (φ ⇔ ψ)))
    (⇔-equiv₂
      (assume ((φ ⊃ ψ) ∧ (ψ ⊃ φ))))
-------------------------------------------------------------------------- ∎

-- Theorem.
⇔-assoc₁
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ⇔ (ψ ⇔ γ)
  → Γ ⊢ (φ ⇔ ψ) ⇔ γ

-- Proof.
⇔-assoc₁ {Γ}{φ = φ}{ψ}{γ} thm =
  ⇔-intro
    (RAA
      (¬-elim
        (¬-intro
          (¬-elim
            (¬-intro
              (¬-elim
                (weaken φ $ weaken (ψ ⇔ γ) $ assume {Γ = Γ , φ ⇔ ψ} (¬ γ))
                (⇔-elim₁
                  (⇔-elim₁
                    (assume {Γ = Γ , φ ⇔ ψ , ¬ γ , ψ ⇔ γ} φ)
                    (weaken φ $ weaken (ψ ⇔ γ)
                        (weaken (¬ γ) $ assume (φ ⇔ ψ))))
                  (⇔-elim₁
                    (assume {Γ = Γ , φ ⇔ ψ , ¬ γ , ψ ⇔ γ} φ)
                    (weaken φ $ weaken (ψ ⇔ γ) $ weaken (¬ γ) $
                      weaken (φ ⇔ ψ) thm)))))
            (⇔-elim₂
              (assume {Γ = Γ , φ ⇔ ψ , ¬ γ} (ψ ⇔ γ))
              (weaken (ψ ⇔ γ) $ weaken (¬ γ) $ weaken (φ ⇔ ψ) thm))))
        (⇔-intro
          (⊥-elim γ
            (¬-elim
              (⊥-elim (¬ ψ)
                (¬-elim
                  (¬-intro -- ¬ φ
                    (¬-elim
                      (weaken φ $ weaken ψ $ assume {Γ = Γ , φ ⇔ ψ} (¬ γ))
                      (⇔-elim₁
                        (⇔-elim₁
                          (assume {Γ = Γ , φ ⇔ ψ , ¬ γ , ψ} φ)
                          (weaken φ
                            (weaken ψ
                              (weaken (¬ γ)
                                (assume (φ ⇔ ψ))))))
                        (⇔-elim₁
                          (assume {Γ = Γ , φ ⇔ ψ , ¬ γ , ψ} φ)
                          (weaken φ $
                            weaken ψ $ weaken (¬ γ) $ weaken (φ ⇔ ψ) thm)))))
                  (⇔-elim₂ -- φ
                    (assume {Γ = Γ , φ ⇔ ψ , ¬  γ} ψ)
                    (weaken ψ (weaken (¬ γ) (assume (φ ⇔ ψ)))))))
              (assume {Γ = Γ , φ ⇔ ψ , ¬ γ} ψ)))
          (⊥-elim ψ
            (¬-elim
              (weaken γ $ assume {Γ = Γ , φ ⇔ ψ} (¬ γ))
              (assume {Γ = Γ , φ ⇔ ψ , ¬ γ} γ))))))
    (⇔-intro
      (⇔-elim₂
        (weaken φ $ assume γ)
        (⇔-elim₁
          (assume {Γ = Γ , γ} φ)
          (weaken φ $ weaken γ thm)))
      (⇔-elim₂
        (⇔-intro
          (weaken ψ $ weaken ψ $ assume γ)
          (weaken γ $ assume {Γ = Γ , γ} ψ))
        (weaken ψ $ weaken γ thm)))
-------------------------------------------------------------------------- ∎

-- Theorem.
⇔-assoc₂
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ⇔ ψ) ⇔ γ
  → Γ ⊢ φ ⇔ (ψ ⇔ γ)

-- Proof.
⇔-assoc₂ {Γ}{φ}{ψ}{γ} thm =
  ⇔-intro
    (⇔-intro
      (⇔-elim₁
        (⇔-intro
          (weaken φ (assume {Γ = Γ , φ} ψ))
          (weaken ψ (weaken ψ (assume φ))))
        (weaken ψ (weaken φ thm)))
      (⇔-elim₁
        (weaken γ (assume φ))
          (⇔-elim₂
            (assume {Γ = Γ , φ} γ)
            (weaken γ (weaken φ thm)))))
    (RAA
      (¬-elim
        (¬-intro
          (¬-elim
            (¬-intro
              (¬-elim
                (weaken γ $ weaken (φ ⇔ ψ) $ assume {Γ = Γ , ψ ⇔ γ} (¬ φ))
                (⇔-elim₂
                  (⇔-elim₂
                    (assume {Γ = Γ , ψ ⇔ γ , ¬ φ , (φ ⇔ ψ)} γ)
                    (weaken γ $ weaken (φ ⇔ ψ) $ weaken (¬ φ) $
                      assume (ψ ⇔ γ)))
                  (⇔-elim₂
                    (assume {Γ = Γ , ψ ⇔ γ , ¬ φ , (φ ⇔ ψ)} γ)
                    (weaken γ $ weaken (φ ⇔ ψ) $ weaken (¬ φ) $
                      weaken (ψ ⇔ γ) thm)))))
            (⇔-elim₁
              (assume {Γ = Γ , ψ ⇔ γ , ¬ φ} (φ ⇔ ψ))
              (weaken (φ ⇔ ψ) (weaken (¬ φ) (weaken (ψ ⇔ γ) thm))))))
        (⇔-intro
          (⊥-elim ψ
            (¬-elim
              (weaken φ $ assume {Γ = Γ , ψ ⇔ γ} (¬ φ))
              (assume {Γ = Γ , ψ ⇔ γ , ¬ φ} φ)))
          (⊥-elim φ
            (¬-elim
              (⊥-elim (¬ ψ)
                (¬-elim
                  (¬-intro
                    (¬-elim
                      (weaken γ $ weaken ψ $ assume {Γ = Γ , ψ ⇔ γ} (¬ φ))
                      (⇔-elim₂
                        (weaken γ $ assume {Γ = Γ , ψ ⇔ γ , ¬ φ} ψ)
                        (⇔-elim₂
                          (assume {Γ = Γ , ψ ⇔ γ , ¬ φ , ψ} γ)
                          (weaken γ $ weaken ψ $ weaken (¬ φ) $
                            weaken (ψ ⇔ γ) thm)))))
                  (⇔-elim₁
                    (assume {Γ = Γ , ψ ⇔ γ , ¬ φ} ψ)
                    (weaken ψ (weaken (¬ φ) (assume (ψ ⇔ γ)))))))
              (assume {Γ = Γ , ψ ⇔ γ , ¬ φ} ψ))))))
-------------------------------------------------------------------------- ∎

-- Theorem.
⇔-assoc
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ⇔ (ψ ⇔ γ)) ⇔ ((φ ⇔ ψ) ⇔ γ)

-- Proof.
⇔-assoc {φ = φ}{ψ}{γ} =
  ⇔-intro
    (⇔-assoc₁ (assume (φ ⇔ ψ ⇔ γ)))
    (⇔-assoc₂ (assume ((φ ⇔ ψ) ⇔ γ)))
-------------------------------------------------------------------------- ∎

-- Theorem.
⇔-comm
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ⇔ ψ
  → Γ ⊢ ψ ⇔ φ

-- Proof.
⇔-comm {Γ}{φ}{ψ} Γ⊢φ⇔ψ =
  ⇔-intro
    (⇔-elim₂ (assume ψ) (weaken ψ Γ⊢φ⇔ψ))
    (⇔-elim₁ (assume φ) (weaken φ Γ⊢φ⇔ψ))
-------------------------------------------------------------------------- ∎

-- Theorem.
⊃-⇔-¬∨
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ (φ ⊃ ψ) ⇔ (¬ φ ∨ ψ)

-- Proof.

⊃-⇔-¬∨ {Γ}{φ}{ψ} =
  ⇔-intro
    (⊃-to-¬∨ (assume (φ ⊃ ψ)))
    (¬∨-to-⊃ (assume (¬ φ ∨ ψ)))
-------------------------------------------------------------------------- ∎

-- Theorem.
bicon₀-thm
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ⇔ ψ → Γ ⊢ ¬ φ
  → Γ ⊢ ¬ ψ
⇔-¬-to-¬ = bicon₀-thm

-- Proof.
bicon₀-thm {Γ}{φ}{ψ} Γ⊢φ⇔ψ Γ⊢¬ψ =
  ¬-equiv₂
    (⊃-intro
      (¬-elim
        (weaken ψ Γ⊢¬ψ)
      (⇔-elim₂
        (assume ψ)
        (weaken ψ Γ⊢φ⇔ψ))))
-------------------------------------------------------------------------- ∎

-- Theorem.
bicon₁-thm
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ φ ⇔ ψ → Γ ⊢ φ
  → Γ ⊢ ¬ ψ
¬⇔-to-¬ = bicon₁-thm

-- Proof.
bicon₁-thm {Γ}{φ}{ψ} Γ⊢¬φ⇔ψ Γ⊢φ =
  ¬-equiv₂
    (⊃-intro
      (¬-elim
        (⇔-elim₂
          (assume ψ)
          (weaken ψ Γ⊢¬φ⇔ψ))
        (weaken ψ Γ⊢φ)))
-------------------------------------------------------------------------- ∎

-- Theorem.
¬-equiv
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ φ ⇔ (φ ⊃ ⊥)

-- Proof.
¬-equiv {Γ}{φ} =
  ⇔-intro
    (¬-equiv₁ (assume (¬ φ)))
    (¬-equiv₂ (assume (φ ⊃ ⊥)))
-------------------------------------------------------------------------- ∎

-- Theorem.
¬¬-equiv
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ (¬ φ) ⇔ φ

-- Proof.
¬¬-equiv {Γ}{φ} =
  ⇔-intro
    (¬¬-equiv₁ (assume (¬ (¬ φ))))
    (¬¬-equiv₂ (assume φ))
-------------------------------------------------------------------------- ∎

-- Theorem.
⊃⊃-⇔-∧⊃
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ⊃ (ψ ⊃ γ)) ⇔ ((φ ∧ ψ) ⊃ γ)

-- Proof.
⊃⊃-⇔-∧⊃ {φ = φ}{ψ}{γ} =
  ⇔-intro
    (⊃⊃-to-∧⊃ (assume (φ ⊃ ψ ⊃ γ)))
    (∧⊃-to-⊃⊃ (assume (φ ∧ ψ ⊃ γ)))
-------------------------------------------------------------------------- ∎

-- Theorem.
⇔-trans
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ γ ⇔ φ
  → Γ ⊢ φ ⇔ ψ
  → Γ ⊢ γ ⇔ ψ
subst⊢⇔₁ = ⇔-trans

-- Proof.
⇔-trans {φ = φ}{ψ}{γ} Γ⊢γ⇔φ Γ⊢φ⇔ψ =
  ⇔-intro
    (⇔-elim₁
      (⇔-elim₁
        (assume γ)
        (weaken γ Γ⊢γ⇔φ))
      (weaken γ Γ⊢φ⇔ψ))
    (⇔-elim₂
      (⇔-elim₂
        (assume ψ)
        (weaken ψ Γ⊢φ⇔ψ))
      (weaken ψ Γ⊢γ⇔φ))
-------------------------------------------------------------------------- ∎
