------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ∨ connective.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module Data.Prop.Theorems.Disjunction (n : ℕ) where

open import Data.Prop.Syntax n
open import Data.Prop.Theorems.Conjunction n using (∧-morgan₁)
open import Data.Prop.Theorems.Implication n using (th244e)

open import Function using (_$_ ; _∘_)


∨-assoc₁ : ∀ {Γ} {φ ψ ω}
         → Γ ⊢ (φ ∨ ψ) ∨ ω
         → Γ ⊢ φ ∨ (ψ ∨ ω)


∨-assoc₂ : ∀ {Γ} {φ ψ ω}
         → Γ ⊢ φ ∨ (ψ ∨ ω)
         → Γ ⊢ (φ ∨ ψ) ∨ ω


∨-comm  : ∀ {Γ} {φ ψ}
        → Γ ⊢ φ ∨ ψ
        → Γ ⊢ ψ ∨ φ


∨-dist₁ : ∀ {Γ} {φ ψ ω}
        → Γ ⊢ φ ∨ (ψ ∧ ω)
        → Γ ⊢ (φ ∨ ψ) ∧ (φ ∨ ω)


∨-dist₂ : ∀ {Γ} {φ ψ ω}
        → Γ ⊢ (φ ∨ ψ) ∧ (φ ∨ ω)
        → Γ ⊢ φ ∨ (ψ ∧ ω)


∨-equiv : ∀ {Γ} {φ ψ}
        → Γ ⊢ φ ∨ ψ
        → Γ ⊢ ¬ (¬ φ ∧ ¬ ψ)


∨-morgan₁ : ∀ {Γ} {φ ψ}
          → Γ ⊢ ¬ (φ ∨ ψ)
          → Γ ⊢ ¬ φ ∧ ¬ ψ


∨-morgan₂ : ∀ {Γ} {φ ψ}
          → Γ ⊢ ¬ φ ∧ ¬ ψ
          → Γ ⊢ ¬ (φ ∨ ψ)


lem1 : ∀ {Γ} {φ ψ}
     → Γ ⊢ ¬ ¬ φ ∨ ¬ ¬ ψ
     → Γ ⊢ φ ∨ ψ


lem2 : ∀ {Γ} {φ ψ}
     → Γ ⊢ (φ ∨ ψ) ∧ ¬ ψ
     → Γ ⊢ φ


resolve₀ : ∀ {Γ} {L C D}
         → Γ ⊢ L ∨ C → Γ ⊢ ¬ L ∨ D
         → Γ ⊢ C ∨ D


resolve₁ : ∀ {Γ} {L C D}
         → Γ ⊢ C ∨ L → Γ ⊢ ¬ L ∨ D
         → Γ ⊢ C ∨ D


resolve₂ : ∀ {Γ} {L C D}
         → Γ ⊢ L ∨ C → Γ ⊢ D ∨ ¬ L
         → Γ ⊢ C ∨ D


resolve₃ : ∀ {Γ} {L C D}
         → Γ ⊢ C ∨ L → Γ ⊢ D ∨ ¬ L
         → Γ ⊢ C ∨ D


resolve₄ : ∀ {Γ} {L C}
         → Γ ⊢ ¬ L ∨ C → Γ ⊢ L
         → Γ ⊢ C


resolve₅ : ∀ {Γ} {L C}
         → Γ ⊢ C ∨ ¬ L
         → Γ ⊢ L
         → Γ ⊢ C


resolve₆ : ∀ {Γ} {L C}
         → Γ ⊢ C ∨ L → Γ ⊢ ¬ L
         → Γ ⊢ C


resolve₇ : ∀ {Γ} {L C}
        → Γ ⊢ L ∨ C → Γ ⊢ ¬ L
        → Γ ⊢ C


resolve₈ : ∀ {Γ} {φ}
         → Γ ⊢ φ → Γ ⊢ ¬ φ
         → Γ ⊢ ⊥


resolve₉ : ∀ {Γ} {φ}
         → Γ ⊢ ¬ φ → Γ ⊢ φ
         → Γ ⊢ ⊥


------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------

∨-assoc₁ {Γ}{φ}{ψ}{ω} =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (⇒-elim
          (⇒-intro
            (∨-elim {Γ  = Γ , φ ∨ ψ}
              (∨-intro₁ (ψ ∨ ω)
                (assume {Γ = Γ , φ ∨ ψ} φ))
              (∨-intro₂ φ
                (∨-intro₁ ω
                  (assume {Γ = Γ , φ ∨ ψ} ψ)))))
          (assume {Γ = Γ} (φ ∨ ψ)))
        (∨-intro₂ φ
          (∨-intro₂ ψ
            (assume {Γ = Γ} ω)))))


∨-assoc₂ {Γ}{φ}{ψ}{ω} =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ ω
          (∨-intro₁ ψ
            (assume {Γ = Γ} φ)))
        (⇒-elim
          (⇒-intro
            (∨-elim {Γ = Γ , ψ ∨ ω}
              (∨-intro₁ ω
                (∨-intro₂ φ (assume {Γ = Γ , ψ ∨ ω} ψ)))
              (∨-intro₂ (φ ∨ ψ) (assume {Γ = Γ , ψ ∨ ω} ω))))
          (assume {Γ = Γ} (ψ ∨ ω)))))


∨-comm {Γ}{φ}{ψ} =
  ⇒-elim $
    ⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₂ ψ
          (assume {Γ = Γ} φ))
        (∨-intro₁ φ $
           assume {Γ = Γ} ψ))


∨-equiv {Γ}{φ}{ψ} seq =
  ¬-intro
    (⇒-elim
      (⇒-intro
        (∨-elim {Γ = Γ , ¬ φ ∧ ¬ ψ}
          (¬-elim
            (weaken φ
              (∧-proj₁
                (assume {Γ = Γ} (¬ φ ∧ ¬ ψ))))
            (assume {Γ = Γ , ¬ φ ∧ ¬ ψ }  φ))
          (¬-elim
            (weaken ψ
              (∧-proj₂
                (assume {Γ = Γ} (¬ φ ∧ ¬ ψ))))
            (assume {Γ = Γ , ¬ φ ∧ ¬ ψ}  ψ))))
      (weaken (¬ φ ∧ ¬ ψ) seq))


∨-dist₁ {Γ}{φ}{ψ}{ω} =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∧-intro
          (∨-intro₁ ψ
            (assume {Γ = Γ} φ))
          (∨-intro₁ ω
            (assume {Γ = Γ} φ)))
        (∧-intro
          (∨-intro₂ φ
            (∧-proj₁
              (assume {Γ = Γ} (ψ ∧ ω))))
          (∨-intro₂ φ
            (∧-proj₂
              (assume {Γ = Γ} (ψ ∧ ω)))))))


∨-dist₂  {Γ}{φ}{ψ}{ω} seq =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ (ψ ∧ ω)
          (assume {Γ = Γ} φ))
        (⇒-elim
          (⇒-intro
            (∨-elim {Γ = Γ , ψ}
              (∨-intro₁ (ψ ∧ ω)
                (assume {Γ = Γ , ψ} φ))
              (∨-intro₂ φ
                (∧-intro
                  (weaken ω
                    (assume {Γ = Γ} ψ))
                  (assume {Γ = Γ , ψ} ω)))))
          (∧-proj₂
            (weaken ψ seq)))))
    (∧-proj₁ seq)


∨-morgan₁ {Γ}{φ}{ψ} =
  ⇒-elim $
    ⇒-intro $
      ∧-intro
        (¬-intro $
          ¬-elim
            (weaken φ $
              assume {Γ = Γ} (¬ (φ ∨ ψ)))
            (∨-intro₁ ψ $
              assume {Γ = Γ , ¬ (φ ∨ ψ)} φ))
        (¬-intro $
          ¬-elim
            (weaken ψ $
              assume {Γ = Γ} (¬ (φ ∨ ψ)))
            (∨-intro₂ φ $
              assume {Γ = Γ , ¬ (φ ∨ ψ)} ψ))


∨-morgan₂ {Γ}{φ}{ψ} seq =
  ¬-intro
    (∨-elim {Γ = Γ}
      (¬-elim
        (weaken φ
          (∧-proj₁ seq))
        (assume {Γ = Γ} φ))
      (¬-elim
        (weaken ψ
          (∧-proj₂ seq))
        (assume {Γ = Γ} ψ)))


lem1 {Γ}{φ}{ψ} =
  ⇒-elim $
    ⇒-intro $
      ∨-elim {Γ = Γ}
        (∨-intro₁ ψ $
          ⇒-elim th244e $ assume {Γ = Γ} $ ¬ ¬ φ)
        (∨-intro₂ φ $
          ⇒-elim th244e $ assume {Γ = Γ} $ ¬ ¬ ψ)


lem2 {Γ}{φ}{ψ} seq =
  ⇒-elim
    (⇒-intro $
      (∨-elim {Γ = Γ}
        (assume {Γ = Γ} φ)
        (⊥-elim φ
          (¬-elim
            (weaken ψ (∧-proj₂ seq))
            (assume {Γ = Γ} ψ)))))
    (∧-proj₁ seq)


resolve₀ {Γ} {L}{C}{D} seq₁ seq₂ =
 lem1 $
   ∧-morgan₁ $
     ¬-intro $
       ¬-elim
         (lem2 {Γ = Γ , ¬ C ∧ ¬ D} $
           ∧-intro
             (weaken (¬ C ∧ ¬ D) seq₂)
             (∧-proj₂ $ assume {Γ = Γ} $ ¬ C ∧ ¬ D))
         (lem2 $
           ∧-intro
             (weaken (¬ C ∧ ¬ D) seq₁)
             (∧-proj₁ $ assume {Γ = Γ} $ ¬ C ∧ ¬ D))


resolve₁ = resolve₀ ∘ ∨-comm


resolve₂ seq₁ seq₂ = resolve₀ seq₁ (∨-comm seq₂)


resolve₃ {Γ} {L}{C}{D} seq₁ seq₂ =  resolve₀ (∨-comm seq₁) (∨-comm seq₂)


resolve₄ {Γ} {L} {C} seq₁ seq₂ =
 ⇒-elim
   (⇒-intro $
     ∨-elim {Γ = Γ}
       (assume {Γ = Γ} C)
       (assume {Γ = Γ} C))
   (resolve₀ {Γ = Γ} {L = L} {C = C} {D = C}
     (∨-intro₁ C seq₂)
     seq₁)


resolve₅ = resolve₄ ∘ ∨-comm


resolve₆ {Γ} {L} {C} seq₁ seq₂ =
 ⇒-elim
   (⇒-intro $
     ∨-elim {Γ = Γ}
       (assume {Γ = Γ}  C)
       (assume {Γ = Γ} C))
   (resolve₀ (∨-comm seq₁) (∨-intro₁ C seq₂))


resolve₇ {Γ} {L} {C} seq₁ seq₂ = resolve₆ (∨-comm seq₁) seq₂


resolve₈ seq₁ seq₂ = ¬-elim seq₂ seq₁

resolve₉ = ¬-elim
