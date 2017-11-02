------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems of ∨ connective.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.PropFormula.Theorems.Disjunction ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Syntax n
open import Data.PropFormula.Theorems.Classical n
open import Data.PropFormula.Properties n

open import Data.PropFormula.Theorems.Conjunction n using ( ∧-dmorgan₁ )
open import Data.PropFormula.Theorems.Implication n using ( vanDalen244e )

open import Function using ( _$_; _∘_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

------------------------------------------------------------------------------

∨-assoc₁
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ∨ (ψ ∨ γ)
  → Γ ⊢ (φ ∨ ψ) ∨ γ

∨-assoc₂
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ∨ ψ) ∨ γ
  → Γ ⊢ φ ∨ (ψ ∨ γ)

∨-assoc
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ∨ (ψ ∨ γ)) ⇔ ((φ ∨ ψ) ∨ γ)

∨-comm
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ∨ ψ
  → Γ ⊢ ψ ∨ φ

∨-dist₁
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ∨ (ψ ∧ γ)
  → Γ ⊢ (φ ∨ ψ) ∧ (φ ∨ γ)

∨-dist₂
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ∨ ψ) ∧ (φ ∨ γ)
  → Γ ⊢ φ ∨ (ψ ∧ γ)

∨-dist
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ∨ (ψ ∧ γ)) ⇔ ((φ ∨ ψ) ∧ (φ ∨ γ))

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
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ∨ ψ → Γ ⊢ ¬ φ ∨ γ
  → Γ ⊢ ψ ∨ γ

resolve₁
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ ψ ∨ φ → Γ ⊢ ¬ φ ∨ γ
  → Γ ⊢ ψ ∨ γ

resolve₂
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ∨ ψ → Γ ⊢ γ ∨ ¬ φ
  → Γ ⊢ ψ ∨ γ

resolve₃
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ ψ ∨ φ → Γ ⊢ γ ∨ ¬ φ
  → Γ ⊢ ψ ∨ γ

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
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ⇒ γ
  → Γ ⊢ φ ∨ ψ
  → Γ ⊢ γ ∨ ψ

subst⊢∨₂
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ ψ ⇒ γ
  → Γ ⊢ φ ∨ ψ
  → Γ ⊢ φ ∨ γ

∨-to-¬⇒
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ∨ ψ
  → Γ ⊢ ¬ φ ⇒ ψ

-- A basic one.

φ∨⊥-to-φ
 : ∀ {Γ} {φ}
 → Γ ⊢ φ ∨ ⊥
 → Γ ⊢ φ

subst⊢∨₁≡
  : ∀ {Γ} {φ ψ γ}
  → φ ≡ γ
  → Γ ⊢ φ ∨ ψ
  → Γ ⊢ γ ∨ ψ

------------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------------

∨-assoc₁ {Γ}{φ}{ψ}{γ} =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ γ
          (∨-intro₁ ψ
            (assume {Γ = Γ} φ)))
        (⇒-elim
          (⇒-intro
            (∨-elim {Γ = Γ , ψ ∨ γ}
              (∨-intro₁ γ
                (∨-intro₂ φ (assume {Γ = Γ , ψ ∨ γ} ψ)))
              (∨-intro₂ (φ ∨ ψ) (assume {Γ = Γ , ψ ∨ γ} γ))))
          (assume {Γ = Γ} (ψ ∨ γ)))))

∨-assoc₂ {Γ}{φ}{ψ}{γ} =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (⇒-elim
          (⇒-intro
            (∨-elim {Γ  = Γ , φ ∨ ψ}
              (∨-intro₁ (ψ ∨ γ)
                (assume {Γ = Γ , φ ∨ ψ} φ))
              (∨-intro₂ φ
                (∨-intro₁ γ
                  (assume {Γ = Γ , φ ∨ ψ} ψ)))))
          (assume {Γ = Γ} (φ ∨ ψ)))
        (∨-intro₂ φ
          (∨-intro₂ ψ
            (assume {Γ = Γ} γ)))))

∨-assoc {Γ}{φ}{ψ}{γ} =
  ⇔-intro
    (∨-assoc₁ (assume {Γ = Γ} (φ ∨ (ψ ∨ γ))))
    (∨-assoc₂ (assume {Γ = Γ} (φ ∨ ψ ∨ γ)))

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

∨-dist₁ {Γ}{φ}{ψ}{γ} =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∧-intro
          (∨-intro₁ ψ
            (assume {Γ = Γ} φ))
          (∨-intro₁ γ
            (assume {Γ = Γ} φ)))
        (∧-intro
          (∨-intro₂ φ
            (∧-proj₁
              (assume {Γ = Γ} (ψ ∧ γ))))
          (∨-intro₂ φ
            (∧-proj₂
              (assume {Γ = Γ} (ψ ∧ γ)))))))

∨-dist₂  {Γ}{φ}{ψ}{γ} Γ⊢⟪φ∨ψ⟫∧⟪φ∨γ⟫ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ (ψ ∧ γ)
          (assume {Γ = Γ} φ))
        (⇒-elim
          (⇒-intro
            (∨-elim {Γ = Γ , ψ}
              (∨-intro₁ (ψ ∧ γ)
                (assume {Γ = Γ , ψ} φ))
              (∨-intro₂ φ
                (∧-intro
                  (weaken γ
                    (assume {Γ = Γ} ψ))
                  (assume {Γ = Γ , ψ} γ)))))
          (∧-proj₂
            (weaken ψ Γ⊢⟪φ∨ψ⟫∧⟪φ∨γ⟫)))))
    (∧-proj₁ Γ⊢⟪φ∨ψ⟫∧⟪φ∨γ⟫)

∨-dist {Γ}{φ}{ψ}{γ} =
  ⇔-intro
    (∨-dist₁ (assume {Γ = Γ} (φ ∨ (ψ ∧ γ))))
    (∨-dist₂ (assume {Γ = Γ} (φ ∨ ψ ∧ (φ ∨ γ))))

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

resolve₀ {Γ}{φ}{ψ}{γ} Γ⊢φ∨ψ Γ⊢¬φ∨γ =
 lem1 $
   ∧-dmorgan₁ $
     ¬-intro $
       ¬-elim
         (lem2 {Γ = Γ , ¬ ψ ∧ ¬ γ} $
           ∧-intro
             (weaken (¬ ψ ∧ ¬ γ) Γ⊢¬φ∨γ)
             (∧-proj₂ $ assume {Γ = Γ} $ ¬ ψ ∧ ¬ γ))
         (lem2 $
           ∧-intro
             (weaken (¬ ψ ∧ ¬ γ) Γ⊢φ∨ψ)
             (∧-proj₁ $ assume {Γ = Γ} $ ¬ ψ ∧ ¬ γ))

resolve₁ = resolve₀ ∘ ∨-comm

resolve₂ Γ⊢φ∨ψ Γ⊢γ∨¬φ =
  resolve₀
    Γ⊢φ∨ψ
    (∨-comm Γ⊢γ∨¬φ)

resolve₃ {Γ}{φ}{ψ}{γ} Γ⊢ψ∨φ Γ⊢γ∨¬φ =
  resolve₀
    (∨-comm Γ⊢ψ∨φ)
    (∨-comm Γ⊢γ∨¬φ)

resolve₄ {Γ}{φ} {ψ} Γ⊢¬φ∨ψ Γ⊢φ =
 ⇒-elim
   (⇒-intro $
     ∨-elim {Γ = Γ}
       (assume {Γ = Γ} ψ)
       (assume {Γ = Γ} ψ))
   (resolve₀ {Γ = Γ} {φ = φ} {ψ = ψ} {γ = ψ}
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

subst⊢∨₁ {Γ}{φ}{ψ}{γ} Γ⊢φ⇒γ Γ⊢φ∨ψ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ ψ (⇒-elim (weaken φ Γ⊢φ⇒γ) (assume {Γ = Γ} φ)))
        (∨-intro₂ γ (assume {Γ = Γ} ψ))))
    Γ⊢φ∨ψ

subst⊢∨₂ {Γ}{φ}{ψ}{γ} Γ⊢ψ⇒γ Γ⊢φ∨ψ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ γ (assume {Γ = Γ} φ))
        (∨-intro₂ φ (⇒-elim (weaken ψ Γ⊢ψ⇒γ) (assume {Γ = Γ} ψ)))))
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

φ∨⊥-to-φ {Γ} {φ} Γ⊢φ∨⊥ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (assume {Γ = Γ} φ)
        (⊥-elim φ (assume {Γ = Γ} ⊥))))
    Γ⊢φ∨⊥

subst⊢∨₁≡ {Γ} {φ}{ψ}{γ} φ≡γ Γ⊢φ∨ψ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ ψ (subst φ≡γ (assume {Γ = Γ} φ)))
        (∨-intro₂ γ (assume {Γ = Γ} ψ))))
    Γ⊢φ∨ψ
