------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ∨ connective.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.Theorems.Disjunction ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Data.Prop.Theorems.Conjunction n using ( ∧-dmorgan₁ )
open import Data.Prop.Theorems.Implication n using ( vanDalen244e )

open import Function                         using ( _$_; _∘_ )

------------------------------------------------------------------------------

∨-assoc₁
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ φ ∨ (ψ ∨ ω)
  → Γ ⊢ (φ ∨ ψ) ∨ ω

∨-assoc₂
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ (φ ∨ ψ) ∨ ω
  → Γ ⊢ φ ∨ (ψ ∨ ω)

∨-assoc
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ (φ ∨ (ψ ∨ ω)) ⇔ ((φ ∨ ψ) ∨ ω)

∨-comm
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ∨ ψ
  → Γ ⊢ ψ ∨ φ

∨-dist₁
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ φ ∨ (ψ ∧ ω)
  → Γ ⊢ (φ ∨ ψ) ∧ (φ ∨ ω)

∨-dist₂
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ (φ ∨ ψ) ∧ (φ ∨ ω)
  → Γ ⊢ φ ∨ (ψ ∧ ω)

∨-dist
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ (φ ∨ (ψ ∧ ω)) ⇔ ((φ ∨ ψ) ∧ (φ ∨ ω))

∨-equiv
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ∨ ψ
  → Γ ⊢ ¬ (¬ φ ∧ ¬ ψ)
∨-to-¬¬∧¬ = ∨-equiv

∨-dmorgan₁
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ (φ ∨ ψ)
  → Γ ⊢ ¬ φ ∧ ¬ ψ
¬∨-to-¬∧¬ = ∨-dmorgan₁

∨-dmorgan₂
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ φ ∧ ¬ ψ
  → Γ ⊢ ¬ (φ ∨ ψ)
¬∧¬-to-¬∨ = ∨-dmorgan₂

∨-dmorgan
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ (φ ∨ ψ) ⇔ (¬ φ ∧ ¬ ψ)

lem1
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ ¬ φ ∨ ¬ ¬ ψ
  → Γ ⊢ φ ∨ ψ
¬¬∨¬¬-to-∨ = lem1

lem2
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ (φ ∨ ψ) ∧ ¬ ψ
  → Γ ⊢ φ

resolve₀
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ φ ∨ ψ → Γ ⊢ ¬ φ ∨ ω
  → Γ ⊢ ψ ∨ ω

resolve₁
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ ψ ∨ φ → Γ ⊢ ¬ φ ∨ ω
  → Γ ⊢ ψ ∨ ω

resolve₂
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ φ ∨ ψ → Γ ⊢ ω ∨ ¬ φ
  → Γ ⊢ ψ ∨ ω

resolve₃
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ ψ ∨ φ → Γ ⊢ ω ∨ ¬ φ
  → Γ ⊢ ψ ∨ ω

resolve₄
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ φ ∨ ψ → Γ ⊢ φ
  → Γ ⊢ ψ

resolve₅
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ψ ∨ ¬ φ
  → Γ ⊢ φ
  → Γ ⊢ ψ

resolve₆
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ψ ∨ φ → Γ ⊢ ¬ φ
  → Γ ⊢ ψ

resolve₇
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ∨ ψ → Γ ⊢ ¬ φ
  → Γ ⊢ ψ

resolve₈
  : ∀ {Γ} {φ}
  → Γ ⊢ φ → Γ ⊢ ¬ φ
  → Γ ⊢ ⊥

resolve₉
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ φ → Γ ⊢ φ
  → Γ ⊢ ⊥

subst⊢∨₁
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ φ ⇒ ω
  → Γ ⊢ φ ∨ ψ
  → Γ ⊢ ω ∨ ψ

subst⊢∨₂
  : ∀ {Γ} {φ ψ ω}
  → Γ ⊢ ψ ⇒ ω
  → Γ ⊢ φ ∨ ψ
  → Γ ⊢ φ ∨ ω

∨-to-¬⇒
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ∨ ψ
  → Γ ⊢ ¬ φ ⇒ ψ

------------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------------

∨-assoc₁ {Γ}{φ}{ψ}{ω} =
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

∨-assoc₂ {Γ}{φ}{ψ}{ω} =
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

∨-assoc {Γ}{φ}{ψ}{ω} =
  ⇔-intro
    (∨-assoc₁ (assume {Γ = Γ} (φ ∨ (ψ ∨ ω))))
    (∨-assoc₂ (assume {Γ = Γ} (φ ∨ ψ ∨ ω)))

∨-comm {Γ}{φ}{ψ} =
  ⇒-elim $
    ⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₂ ψ
          (assume {Γ = Γ} φ))
        (∨-intro₁ φ $
           assume {Γ = Γ} ψ))

∨-equiv {Γ}{φ}{ψ} Γ⊢φ∨ψ =
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
      (weaken (¬ φ ∧ ¬ ψ) Γ⊢φ∨ψ))

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

∨-dist₂  {Γ}{φ}{ψ}{ω} Γ⊢⟪φ∨ψ⟫∧⟪φ∨ω⟫ =
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
            (weaken ψ Γ⊢⟪φ∨ψ⟫∧⟪φ∨ω⟫)))))
    (∧-proj₁ Γ⊢⟪φ∨ψ⟫∧⟪φ∨ω⟫)

∨-dist {Γ}{φ}{ψ}{ω} =
  ⇔-intro
    (∨-dist₁ (assume {Γ = Γ} (φ ∨ (ψ ∧ ω))))
    (∨-dist₂ (assume {Γ = Γ} (φ ∨ ψ ∧ (φ ∨ ω))))

∨-dmorgan₁ {Γ}{φ}{ψ} =
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

∨-dmorgan₂ {Γ}{φ}{ψ} Γ⊢¬φ∧¬ψ  =
  ¬-intro
    (∨-elim {Γ = Γ}
      (¬-elim
        (weaken φ
          (∧-proj₁ Γ⊢¬φ∧¬ψ ))
        (assume {Γ = Γ} φ))
      (¬-elim
        (weaken ψ
          (∧-proj₂ Γ⊢¬φ∧¬ψ ))
        (assume {Γ = Γ} ψ)))

∨-dmorgan {Γ}{φ}{ψ} =
  ⇔-intro
    (∨-dmorgan₁
      (assume {Γ = Γ} (¬ (φ ∨ ψ))))
    (∨-dmorgan₂
      (assume {Γ = Γ} (¬ φ ∧ ¬ ψ)))

lem1 {Γ}{φ}{ψ} =
  ⇒-elim $
    ⇒-intro $
      ∨-elim {Γ = Γ}
        (∨-intro₁ ψ $
          ⇒-elim vanDalen244e $ assume {Γ = Γ} $ ¬ ¬ φ)
        (∨-intro₂ φ $
          ⇒-elim vanDalen244e $ assume {Γ = Γ} $ ¬ ¬ ψ)

lem2 {Γ}{φ}{ψ} Γ⊢⟪φ∨ψ⟫∧¬ψ =
  ⇒-elim
    (⇒-intro $
      (∨-elim {Γ = Γ}
        (assume {Γ = Γ} φ)
        (⊥-elim φ
          (¬-elim
            (weaken ψ (∧-proj₂ Γ⊢⟪φ∨ψ⟫∧¬ψ))
            (assume {Γ = Γ} ψ)))))
    (∧-proj₁ Γ⊢⟪φ∨ψ⟫∧¬ψ)

resolve₀ {Γ}{φ}{ψ}{ω} Γ⊢φ∨ψ Γ⊢¬φ∨ω =
 lem1 $
   ∧-dmorgan₁ $
     ¬-intro $
       ¬-elim
         (lem2 {Γ = Γ , ¬ ψ ∧ ¬ ω} $
           ∧-intro
             (weaken (¬ ψ ∧ ¬ ω) Γ⊢¬φ∨ω)
             (∧-proj₂ $ assume {Γ = Γ} $ ¬ ψ ∧ ¬ ω))
         (lem2 $
           ∧-intro
             (weaken (¬ ψ ∧ ¬ ω) Γ⊢φ∨ψ)
             (∧-proj₁ $ assume {Γ = Γ} $ ¬ ψ ∧ ¬ ω))

resolve₁ = resolve₀ ∘ ∨-comm

resolve₂ Γ⊢φ∨ψ Γ⊢ω∨¬φ =
  resolve₀
    Γ⊢φ∨ψ
    (∨-comm Γ⊢ω∨¬φ)

resolve₃ {Γ}{φ}{ψ}{ω} Γ⊢ψ∨φ Γ⊢ω∨¬φ =
  resolve₀
    (∨-comm Γ⊢ψ∨φ)
    (∨-comm Γ⊢ω∨¬φ)

resolve₄ {Γ}{φ} {ψ} Γ⊢¬φ∨ψ Γ⊢φ =
 ⇒-elim
   (⇒-intro $
     ∨-elim {Γ = Γ}
       (assume {Γ = Γ} ψ)
       (assume {Γ = Γ} ψ))
   (resolve₀ {Γ = Γ} {φ = φ} {ψ = ψ} {ω = ψ}
     (∨-intro₁ ψ Γ⊢φ)
     Γ⊢¬φ∨ψ)

resolve₅ = resolve₄ ∘ ∨-comm

resolve₆ {Γ}{φ}{ψ} Γ⊢ψ∨φ Γ⊢¬φ =
 ⇒-elim
   (⇒-intro $
     ∨-elim {Γ = Γ}
       (assume {Γ = Γ} ψ)
       (assume {Γ = Γ} ψ))
   (resolve₀ (∨-comm Γ⊢ψ∨φ) (∨-intro₁ ψ Γ⊢¬φ))

resolve₇ {Γ}{φ}{ψ} Γ⊢φ∨ψ Γ⊢¬φ = resolve₆ (∨-comm Γ⊢φ∨ψ) Γ⊢¬φ

resolve₈ Γ⊢φ Γ⊢¬φ = ¬-elim Γ⊢¬φ Γ⊢φ

resolve₉ = ¬-elim

subst⊢∨₁ {Γ}{φ}{ψ}{ω} Γ⊢φ⇒ω Γ⊢φ∨ψ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ ψ (⇒-elim (weaken φ Γ⊢φ⇒ω) (assume {Γ = Γ} φ)))
        (∨-intro₂ ω (assume {Γ = Γ} ψ))))
    Γ⊢φ∨ψ

subst⊢∨₂ {Γ}{φ}{ψ}{ω} Γ⊢ψ⇒ω Γ⊢φ∨ψ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ ω (assume {Γ = Γ} φ))
        (∨-intro₂ φ (⇒-elim (weaken ψ Γ⊢ψ⇒ω) (assume {Γ = Γ} ψ)))))
    Γ⊢φ∨ψ

∨-to-¬⇒ {Γ}{φ}{ψ} Γ⊢φ∨ψ =
  ⇒-intro
    (⇒-elim
      (⇒-intro
        (∨-elim {Γ = Γ , ¬ φ}
          (⊥-elim ψ
            (¬-elim
              (weaken φ
                (assume {Γ = Γ} (¬ φ)))
            (assume {Γ = Γ , ¬ φ} φ)))
          (assume {Γ = Γ , ¬ φ} ψ)))
      (weaken (¬ φ) Γ⊢φ∨ψ))
