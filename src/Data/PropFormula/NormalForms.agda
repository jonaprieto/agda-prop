------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Normal Forms.
------------------------------------------------------------------------------

open import Data.Nat using (ℕ; suc; zero; _+_;_*_) renaming (_⊔_ to max )

module Data.PropFormula.NormalForms (n : ℕ) where

------------------------------------------------------------------------------

open import Data.Bool.Base
  using ( Bool; true; false; if_then_else_; not)
  renaming (_∧_ to _and_; _∨_ to _or_)

open import Data.Fin  using ( Fin; #_ )
open import Data.List using ( List; [_]; [];  _++_; _∷_ ; concatMap; map )

open import Data.PropFormula.Properties n using ( subst )
open import Data.PropFormula.Syntax n
open import Data.PropFormula.Views  n

open import Relation.Nullary using (yes; no)
open import Data.PropFormula.Theorems n

open import Function using ( _∘_; _$_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; sym )

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Negation Normal Form (NNF)
------------------------------------------------------------------------------

nnf′ : ℕ → PropFormula → PropFormula
nnf′ (suc n) φ
  with n-view φ
...  | conj φ₁ φ₂   = nnf′ n φ₁ ∧ nnf′ n φ₂
...  | disj φ₁ φ₂   = nnf′ n φ₁ ∨ nnf′ n φ₂
...  | impl φ₁ φ₂   = nnf′ n ((¬ φ₁) ∨ φ₂)
...  | biimpl φ₁ φ₂ = nnf′ n ((φ₁ ⇒ φ₂) ∧ (φ₂ ⇒ φ₁))
...  | nconj φ₁ φ₂  = nnf′ n ((¬ φ₁) ∨ (¬ φ₂))
...  | ndisj φ₁ φ₂  = nnf′ n ((¬ φ₁) ∧ (¬ φ₂))
...  | nneg φ₁      = nnf′ n φ₁
...  | nimpl φ₁ φ₂  = nnf′ n (¬ (φ₂ ∨ (¬ φ₁)))
...  | nbiim φ₁ φ₂  = nnf′ n (¬ ((φ₁ ⇒ φ₂) ∧ (φ₂ ⇒ φ₁)))
...  | ntop         = ⊥
...  | nbot         = ⊤
...  | other .φ     = φ
nnf′ zero φ         = φ


thm-nnf′
  : ∀ {Γ} {φ}
  → (n : ℕ)
  → Γ ⊢ φ
  → Γ ⊢ nnf′ n φ

thm-nnf′ {Γ} {φ} (suc n) Γ⊢φ
  with n-view φ
...  | conj φ₁ φ₂ =
  ∧-intro
    (thm-nnf′ n (∧-proj₁ Γ⊢φ))
    (thm-nnf′ n (∧-proj₂ Γ⊢φ))
...  | disj φ₁ φ₂ =
  (⇒-elim
    (⇒-intro
     (∨-elim {Γ = Γ}
       (∨-intro₁
         (nnf′ n φ₂)
         (thm-nnf′ n (assume {Γ = Γ} φ₁)))
       (∨-intro₂
         (nnf′ n φ₁)
         (thm-nnf′ n (assume {Γ = Γ} φ₂)))))
      Γ⊢φ)
...  | impl φ₁ φ₂   = thm-nnf′ n (⇒-to-¬∨ Γ⊢φ)
...  | biimpl φ₁ φ₂ = thm-nnf′ n (⇔-equiv₁ Γ⊢φ)
...  | nconj φ₁ φ₂  = thm-nnf′ n (¬∧-to-¬∨¬ Γ⊢φ)
...  | ndisj φ₁ φ₂  = thm-nnf′ n (¬∨-to-¬∧¬ Γ⊢φ)
...  | nneg φ₁      = thm-nnf′ n (¬¬-equiv₁ Γ⊢φ)
...  | nimpl φ₁ φ₂  = thm-nnf′ n (subst⊢¬ helper Γ⊢φ)
  where
    helper : Γ ⊢ φ₂ ∨ ¬ φ₁ ⇒ (φ₁ ⇒ φ₂)
    helper = ⇒-intro (¬∨-to-⇒ (∨-comm (assume {Γ = Γ} (φ₂ ∨ ¬ φ₁))))
...  | nbiim φ₁ φ₂  =
  thm-nnf′ n
    (subst⊢¬
      (⇒-intro
        (⇔-equiv₂
          (assume {Γ = Γ} ((φ₁ ⇒ φ₂) ∧ (φ₂ ⇒ φ₁)))))
          Γ⊢φ)
...  | ntop       = ¬-elim Γ⊢φ ⊤-intro
...  | nbot       = ⊤-intro
...  | other .φ   = Γ⊢φ
thm-nnf′ {Γ} {φ} zero Γ⊢φ = Γ⊢φ


nnf-complexity : PropFormula → ℕ
nnf-complexity φ with n-view φ
... | conj φ₁ φ₂   = nnf-complexity φ₁ + nnf-complexity φ₂ + 1
... | disj φ₁ φ₂   = nnf-complexity φ₁ + nnf-complexity φ₂ + 1
... | impl φ₁ φ₂   = 2 * nnf-complexity φ₁  + nnf-complexity φ₂ + 1
... | biimpl φ₁ φ₂ = 2 * (nnf-complexity φ₁ + nnf-complexity φ₂) + 3
... | nconj φ₁ φ₂  = nnf-complexity (¬ φ₁) + nnf-complexity (¬ φ₂) + 1
... | ndisj φ₁ φ₂  = nnf-complexity (¬ φ₁) + nnf-complexity (¬ φ₂) + 1
... | nneg φ₁      = nnf-complexity (¬ φ₁) + 1
... | nimpl φ₁ φ₂  = nnf-complexity φ₁ + nnf-complexity (¬ φ₂) + 3
... | nbiim φ₁ φ₂  = nnf-complexity φ₁ + nnf-complexity φ₂ +
                     nnf-complexity (¬ φ₁) + nnf-complexity (¬ φ₂) + 8
... | ntop         = 1
... | nbot         = 1
... | other .φ     = 1

nnf : PropFormula → PropFormula
nnf φ = nnf′ (nnf-complexity φ) φ

thm-nnf
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ nnf φ

thm-nnf {Γ} {φ} Γ⊢φ = thm-nnf′ (nnf-complexity φ) Γ⊢φ

postulate
  thm-inv-nnf
    : ∀ {Γ} {φ}
    → Γ ⊢ nnf φ
    → Γ ⊢ φ

------------------------------------------------------------------------------
-- Disjunctive Normal Form (DNF)
------------------------------------------------------------------------------

dist-∧ : PropFormula → PropFormula
dist-∧ φ with d-view-aux φ
... | case₁ φ₁ φ₂ φ₃ = dist-∧ (φ₁ ∧ φ₃) ∨ dist-∧ (φ₂ ∧ φ₃)
... | case₂ φ₁ φ₂ φ₃ = dist-∧ (φ₁ ∧ φ₂) ∨ dist-∧ (φ₁ ∧ φ₃)
... | other .φ       = φ

thm-dist-∧
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ dist-∧ φ

thm-dist-∧ {Γ} {φ} Γ⊢φ with d-view-aux φ
thm-dist-∧ {Γ} {.((φ ∨ ψ) ∧ γ)} Γ⊢⟨φ∨ψ⟩∧γ | case₁ φ ψ γ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ (dist-∧ (ψ ∧ γ))
          (thm-dist-∧
            (∧-intro
              (assume {Γ = Γ} φ)
              (weaken φ (∧-proj₂ Γ⊢⟨φ∨ψ⟩∧γ)))))
        (∨-intro₂ (dist-∧ (φ ∧ γ))
          (thm-dist-∧
            (∧-intro
              (assume {Γ = Γ} ψ)
              (weaken ψ (∧-proj₂ Γ⊢⟨φ∨ψ⟩∧γ)))))))
     (∧-proj₁ Γ⊢⟨φ∨ψ⟩∧γ)
thm-dist-∧ {Γ} {.(φ ∧ (ψ ∨ γ))} Γ⊢φ∧⟨ψ∨γ⟩ | case₂ φ ψ γ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ (dist-∧ (φ ∧ γ))
          (thm-dist-∧
            (∧-intro
              (weaken ψ (∧-proj₁ Γ⊢φ∧⟨ψ∨γ⟩))
              (assume {Γ = Γ} ψ))))
        (∨-intro₂ (dist-∧ (φ ∧ ψ))
          (thm-dist-∧
            (∧-intro
              (weaken γ (∧-proj₁ Γ⊢φ∧⟨ψ∨γ⟩))
              (assume {Γ = Γ} γ))))))
    (∧-proj₂ Γ⊢φ∧⟨ψ∨γ⟩)
thm-dist-∧ {Γ} {.φ} Γ⊢φ             | other φ     = Γ⊢φ


dist : PropFormula → PropFormula
dist φ with d-view φ
dist .(φ ∧ ψ) | conj φ ψ = dist-∧ (dist φ ∧ dist ψ)
dist .(φ ∨ ψ) | disj φ ψ = dist φ ∨ dist ψ
dist φ        | other .φ = φ

thm-dist
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ dist φ

thm-dist {Γ} {φ} Γ⊢φ with d-view φ
thm-dist {Γ} {φ ∧ ψ} Γ⊢φ∧ψ | conj .φ .ψ =
  thm-dist-∧
    (∧-intro
      (thm-dist (∧-proj₁ Γ⊢φ∧ψ))
      (thm-dist (∧-proj₂ Γ⊢φ∧ψ)))
thm-dist {Γ} {φ ∨ ψ} Γ⊢φ∨ψ | disj .φ .ψ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ (dist ψ) (thm-dist (assume {Γ = Γ} φ)))
        (∨-intro₂ (dist φ) (thm-dist (assume {Γ = Γ} ψ)))))
    Γ⊢φ∨ψ
thm-dist {Γ} {φ} Γ⊢φ       | other .φ   = Γ⊢φ

dnf : PropFormula → PropFormula
dnf = dist ∘ nnf

thm-dnf
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ dnf φ

thm-dnf = thm-dist ∘ thm-nnf

postulate
  thm-inv-dnf
    : ∀ {Γ} {φ}
    → Γ ⊢ dnf φ
    → Γ ⊢ φ

------------------------------------------------------------------------------
-- Conjunctive Normal Forms (CNF)
------------------------------------------------------------------------------

dist-∨ : PropFormula → PropFormula
dist-∨ φ with c-view-aux φ
dist-∨ .((φ₁ ∧ φ₂) ∨ φ₃) | case₁ φ₁ φ₂ φ₃ = dist-∨ (φ₁ ∨ φ₃) ∧ dist-∨ (φ₂ ∨ φ₃)
dist-∨ .(φ₁ ∨ (φ₂ ∧ φ₃)) | case₂ φ₁ φ₂ φ₃ = dist-∨ (φ₁ ∨ φ₂) ∧ dist-∨ (φ₁ ∨ φ₃)
dist-∨ φ                 | other .φ       = φ


thm-dist-∨
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ dist-∨ φ

thm-dist-∨ {Γ} {φ} Γ⊢φ with c-view-aux φ
thm-dist-∨ {Γ} {.((φ ∧ ψ) ∨ γ)} Γ⊢φ | case₁ φ ψ γ =
  ∧-intro
   (thm-dist-∨ (∧-proj₁ helper))
   (thm-dist-∨ (∧-proj₂ helper))
  where
    helper : Γ ⊢ (φ ∨ γ) ∧ (ψ ∨ γ)
    helper =
      ∧-intro
        (∨-comm  (∧-proj₁ (∨-dist₁ (∨-comm Γ⊢φ))))
        (∨-comm (∧-proj₂ (∨-dist₁ (∨-comm Γ⊢φ))))
thm-dist-∨ {Γ} {.(φ ∨ (ψ ∧ γ))} Γ⊢φ | case₂ φ ψ γ =
  ∧-intro
    (thm-dist-∨ (∧-proj₁ (∨-dist₁ Γ⊢φ)))
    (thm-dist-∨ (∧-proj₂ (∨-dist₁ Γ⊢φ)))
thm-dist-∨ {Γ} {.φ}             Γ⊢φ | other φ     = Γ⊢φ


dist′ : PropFormula → PropFormula
dist′ φ with d-view φ
dist′ .(φ ∧ ψ) | conj φ ψ = dist′ φ ∧ dist′ ψ
dist′ .(φ ∨ ψ) | disj φ ψ = dist-∨ ((dist′ φ) ∨ (dist′ ψ))
dist′ φ        | other .φ = φ

thm-dist′
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ dist′ φ

thm-dist′ {Γ} {φ} Γ⊢φ with d-view φ
thm-dist′ {Γ} {.(φ ∧ ψ)} Γ⊢φ∧ψ | conj φ ψ =
  ∧-intro (thm-dist′ (∧-proj₁ Γ⊢φ∧ψ)) (thm-dist′ (∧-proj₂ Γ⊢φ∧ψ))
thm-dist′ {Γ} {.(φ ∨ ψ)} Γ⊢φ∨ψ | disj φ ψ =
  thm-dist-∨
    (⇒-elim
      (⇒-intro
        (∨-elim {Γ = Γ}
          (∨-intro₁ (dist′ ψ) (thm-dist′ (assume {Γ = Γ} φ)))
          (∨-intro₂ (dist′ φ) (thm-dist′ (assume {Γ = Γ} ψ)))))
      Γ⊢φ∨ψ)
thm-dist′ {Γ} {.φ} Γ⊢φ         | other φ  = Γ⊢φ

cnf : PropFormula → PropFormula
cnf = dist′ ∘ nnf

thm-cnf
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ cnf φ

thm-cnf = thm-dist′ ∘ thm-nnf

postulate
  thm-inv-cnf
    : ∀ {Γ} {φ}
    → Γ ⊢ cnf φ
    → Γ ⊢ φ
