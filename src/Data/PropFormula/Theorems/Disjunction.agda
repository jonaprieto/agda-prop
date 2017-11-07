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

-- Proof.

-------------------------------------------------------------------------- ■


-- Theorem.
∨-assoc₁
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ∨ (ψ ∨ γ)
  → Γ ⊢ (φ ∨ ψ) ∨ γ

-- Proof.
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

-------------------------------------------------------------------------- ■

-- Theorem.
∨-assoc₂
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ∨ ψ) ∨ γ
  → Γ ⊢ φ ∨ (ψ ∨ γ)

-- Proof.
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
-------------------------------------------------------------------------- ■

-- Theorem.
∨-assoc
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ∨ (ψ ∨ γ)) ⇔ ((φ ∨ ψ) ∨ γ)

-- Proof.
∨-assoc {Γ}{φ}{ψ}{γ} =
  ⇔-intro
    (∨-assoc₁ (assume {Γ = Γ} (φ ∨ (ψ ∨ γ))))
    (∨-assoc₂ (assume {Γ = Γ} (φ ∨ ψ ∨ γ)))
-------------------------------------------------------------------------- ■

-- Theorem.
∨-comm
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ∨ ψ
  → Γ ⊢ ψ ∨ φ

-- Proof.
∨-comm {Γ}{φ}{ψ} =
  ⇒-elim $
    ⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₂ ψ
          (assume {Γ = Γ} φ))
        (∨-intro₁ φ $
           assume {Γ = Γ} ψ))
-------------------------------------------------------------------------- ■

-- Theorem.
∨-dist₁
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ∨ (ψ ∧ γ)
  → Γ ⊢ (φ ∨ ψ) ∧ (φ ∨ γ)

-- Proof.
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
-------------------------------------------------------------------------- ■

-- Theorem.
∨-dist₂
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ∨ ψ) ∧ (φ ∨ γ)
  → Γ ⊢ φ ∨ (ψ ∧ γ)

-- Proof.
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
-------------------------------------------------------------------------- ■

-- Theorem.
∨-dist
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ (φ ∨ (ψ ∧ γ)) ⇔ ((φ ∨ ψ) ∧ (φ ∨ γ))

-- Proof.
∨-dist {Γ}{φ}{ψ}{γ} =
  ⇔-intro
    (∨-dist₁ (assume {Γ = Γ} (φ ∨ (ψ ∧ γ))))
    (∨-dist₂ (assume {Γ = Γ} (φ ∨ ψ ∧ (φ ∨ γ))))
-------------------------------------------------------------------------- ■

-- Theorem.
∨-equiv
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ∨ ψ
  → Γ ⊢ ¬ (¬ φ ∧ ¬ ψ)
∨-to-¬¬∧¬ = ∨-equiv

-- Proof.
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
-------------------------------------------------------------------------- ■

-- Theorem.
∨-dmorgan₁
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ (φ ∨ ψ)
  → Γ ⊢ ¬ φ ∧ ¬ ψ
¬∨-to-¬∧¬ = ∨-dmorgan₁

-- Proof.
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
-------------------------------------------------------------------------- ■

-- Theorem.
∨-dmorgan₂
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ φ ∧ ¬ ψ
  → Γ ⊢ ¬ (φ ∨ ψ)
¬∧¬-to-¬∨ = ∨-dmorgan₂

-- Proof.
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
-------------------------------------------------------------------------- ■

-- Theorem.
∨-dmorgan
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ (φ ∨ ψ) ⇔ (¬ φ ∧ ¬ ψ)
¬∨-⇔-¬∧¬ = ∨-dmorgan

-- Proof.
∨-dmorgan {Γ}{φ}{ψ} =
  ⇔-intro
    (∨-dmorgan₁
      (assume {Γ = Γ} (¬ (φ ∨ ψ))))
    (∨-dmorgan₂
      (assume {Γ = Γ} (¬ φ ∧ ¬ ψ)))
-------------------------------------------------------------------------- ■

-- Theorem.
lem1
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ ¬ φ ∨ ¬ ¬ ψ
  → Γ ⊢ φ ∨ ψ
¬¬∨¬¬-to-∨ = lem1

-- Proof.
lem1 {Γ}{φ}{ψ} =
  ⇒-elim $
    ⇒-intro $
      ∨-elim {Γ = Γ}
        (∨-intro₁ ψ $
          ⇒-elim vanDalen244e $ assume {Γ = Γ} $ ¬ ¬ φ)
        (∨-intro₂ φ $
          ⇒-elim vanDalen244e $ assume {Γ = Γ} $ ¬ ¬ ψ)
-------------------------------------------------------------------------- ■

-- Theorem.
lem2
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ (φ ∨ ψ) ∧ ¬ ψ
  → Γ ⊢ φ

-- Proof.
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
-------------------------------------------------------------------------- ■

-- Theorem.
resolve₀
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ∨ ψ → Γ ⊢ ¬ φ ∨ γ
  → Γ ⊢ ψ ∨ γ

-- Proof.
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
-------------------------------------------------------------------------- ■

-- Theorem.
resolve₁
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ ψ ∨ φ → Γ ⊢ ¬ φ ∨ γ
  → Γ ⊢ ψ ∨ γ

-- Proof.
resolve₁ = resolve₀ ∘ ∨-comm
-------------------------------------------------------------------------- ■

-- Theorem.
resolve₂
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ∨ ψ → Γ ⊢ γ ∨ ¬ φ
  → Γ ⊢ ψ ∨ γ

-- Proof.
resolve₂ Γ⊢φ∨ψ Γ⊢γ∨¬φ =
  resolve₀
    Γ⊢φ∨ψ
    (∨-comm Γ⊢γ∨¬φ)
-------------------------------------------------------------------------- ■

-- Theorem.
resolve₃
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ ψ ∨ φ → Γ ⊢ γ ∨ ¬ φ
  → Γ ⊢ ψ ∨ γ

-- Proof.
resolve₃ {Γ}{φ}{ψ}{γ} Γ⊢ψ∨φ Γ⊢γ∨¬φ =
  resolve₀
    (∨-comm Γ⊢ψ∨φ)
    (∨-comm Γ⊢γ∨¬φ)
-------------------------------------------------------------------------- ■

-- Theorem.
resolve₄
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ¬ φ ∨ ψ → Γ ⊢ φ
  → Γ ⊢ ψ

-- Proof.
resolve₄ {Γ}{φ} {ψ} Γ⊢¬φ∨ψ Γ⊢φ =
 ⇒-elim
   (⇒-intro $
     ∨-elim {Γ = Γ}
       (assume {Γ = Γ} ψ)
       (assume {Γ = Γ} ψ))
   (resolve₀ {Γ = Γ} {φ = φ} {ψ = ψ} {γ = ψ}
     (∨-intro₁ ψ Γ⊢φ)
     Γ⊢¬φ∨ψ)
-------------------------------------------------------------------------- ■

-- Theorem.
resolve₅
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ψ ∨ ¬ φ
  → Γ ⊢ φ
  → Γ ⊢ ψ

-- Proof.
resolve₅ = resolve₄ ∘ ∨-comm
-------------------------------------------------------------------------- ■

-- Theorem.
resolve₆
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ψ ∨ φ → Γ ⊢ ¬ φ
  → Γ ⊢ ψ

-- Proof.
resolve₆ {Γ}{φ}{ψ} Γ⊢ψ∨φ Γ⊢¬φ =
 ⇒-elim
   (⇒-intro $
     ∨-elim {Γ = Γ}
       (assume {Γ = Γ} ψ)
       (assume {Γ = Γ} ψ))
   (resolve₀ (∨-comm Γ⊢ψ∨φ) (∨-intro₁ ψ Γ⊢¬φ))
-------------------------------------------------------------------------- ■

-- Theorem.
resolve₇
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ∨ ψ → Γ ⊢ ¬ φ
  → Γ ⊢ ψ

-- Proof.
resolve₇ {Γ}{φ}{ψ} Γ⊢φ∨ψ Γ⊢¬φ = resolve₆ (∨-comm Γ⊢φ∨ψ) Γ⊢¬φ
-------------------------------------------------------------------------- ■

-- Theorem.
resolve₈
  : ∀ {Γ} {φ}
  → Γ ⊢ φ → Γ ⊢ ¬ φ
  → Γ ⊢ ⊥

-- Proof.
resolve₈ Γ⊢φ Γ⊢¬φ = ¬-elim Γ⊢¬φ Γ⊢φ
-------------------------------------------------------------------------- ■

-- Theorem.
resolve₉
  : ∀ {Γ} {φ}
  → Γ ⊢ ¬ φ → Γ ⊢ φ
  → Γ ⊢ ⊥

-- Proof.
resolve₉ = ¬-elim
-------------------------------------------------------------------------- ■

-- Theorem.
subst⊢∨₁
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ φ ⇒ γ
  → Γ ⊢ φ ∨ ψ
  → Γ ⊢ γ ∨ ψ

-- Proof.
subst⊢∨₁ {Γ}{φ}{ψ}{γ} Γ⊢φ⇒γ Γ⊢φ∨ψ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ ψ (⇒-elim (weaken φ Γ⊢φ⇒γ) (assume {Γ = Γ} φ)))
        (∨-intro₂ γ (assume {Γ = Γ} ψ))))
    Γ⊢φ∨ψ
-------------------------------------------------------------------------- ■

-- Theorem.
subst⊢∨₂
  : ∀ {Γ} {φ ψ γ}
  → Γ ⊢ ψ ⇒ γ
  → Γ ⊢ φ ∨ ψ
  → Γ ⊢ φ ∨ γ

-- Proof.
subst⊢∨₂ {Γ}{φ}{ψ}{γ} Γ⊢ψ⇒γ Γ⊢φ∨ψ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ γ (assume {Γ = Γ} φ))
        (∨-intro₂ φ (⇒-elim (weaken ψ Γ⊢ψ⇒γ) (assume {Γ = Γ} ψ)))))
    Γ⊢φ∨ψ
-------------------------------------------------------------------------- ■

-- Theorem.
∨-to-¬⇒
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ ∨ ψ
  → Γ ⊢ ¬ φ ⇒ ψ

-- Proof.
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
-------------------------------------------------------------------------- ■

-- Theorem.
φ∨⊥-to-φ
 : ∀ {Γ} {φ}
 → Γ ⊢ φ ∨ ⊥
 → Γ ⊢ φ

-- Proof.
φ∨⊥-to-φ {Γ} {φ} Γ⊢φ∨⊥ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (assume {Γ = Γ} φ)
        (⊥-elim φ (assume {Γ = Γ} ⊥))))
    Γ⊢φ∨⊥
-------------------------------------------------------------------------- ■

-- Theorem.
subst⊢∨₁≡
  : ∀ {Γ} {φ ψ γ}
  → φ ≡ γ
  → Γ ⊢ φ ∨ ψ
  → Γ ⊢ γ ∨ ψ

-- Proof.
subst⊢∨₁≡ {Γ} {φ}{ψ}{γ} φ≡γ Γ⊢φ∨ψ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ ψ (subst φ≡γ (assume {Γ = Γ} φ)))
        (∨-intro₂ γ (assume {Γ = Γ} ψ))))
    Γ⊢φ∨ψ
-------------------------------------------------------------------------- ■
