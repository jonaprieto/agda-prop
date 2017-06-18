------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Normal Forms.
------------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module Data.Prop.NormalForms (n : ℕ) where

------------------------------------------------------------------------------

open import Data.Nat.Base public
open import Data.Fin  using ( Fin; #_ )
open import Data.List using ( List; [_]; [];  _++_; _∷_ ; concatMap; map )
open import Data.Prop.Properties n using ( subst )
open import Data.Prop.Syntax n
open import Data.Prop.Views  n

open import Relation.Nullary using (yes; no)
open import Data.Prop.Theorems n

open import Function using ( _∘_; _$_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; sym )

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Negation Normal Form (NNF)
------------------------------------------------------------------------------

nnf′ : ℕ → Prop → Prop
nnf′ (suc n) φ
  with n-view φ
...  | conj x y   = nnf′ n x ∧ nnf′ n y
...  | disj x y   = nnf′ n x ∨ nnf′ n y
...  | impl x y   = nnf′ n ((¬ x) ∨ y)
...  | biimpl x y = nnf′ n ((x ⇒ y) ∧ (y ⇒ x))
...  | nconj x y  = nnf′ n ((¬ x) ∨ (¬ y))
...  | ndisj x y  = nnf′ n ((¬ x) ∧ (¬ y))
...  | nneg x     = nnf′ n x
...  | ntop       = ⊥
...  | nbot       = ⊤
...  | nimpl x y  = nnf′ n (¬ (y ∨ (¬ x)))
...  | nbiim x y  = nnf′ n (¬ ((x ⇒ y) ∧ (y ⇒ x)))
...  | other .φ   = φ
nnf′ zero φ       = φ


thm-nnf′
  : ∀ {Γ} {φ}
  → (n : ℕ)
  → Γ ⊢ φ
  → Γ ⊢ nnf′ n φ

thm-nnf′ {Γ} {φ} (suc n) Γ⊢φ
  with n-view φ
...  | conj x y = ∧-intro (thm-nnf′ n (∧-proj₁ Γ⊢φ)) (thm-nnf′ n (∧-proj₂ Γ⊢φ))
...  | disj x y =
  (⇒-elim
    (⇒-intro
     (∨-elim {Γ = Γ}
       (∨-intro₁
         (nnf′ n y)
         (thm-nnf′ n (assume {Γ = Γ} x)))
       (∨-intro₂
         (nnf′ n x)
         (thm-nnf′ n (assume {Γ = Γ} y)))))
      Γ⊢φ)
...  | impl x y   = thm-nnf′ n (⇒-to-¬∨ Γ⊢φ)
...  | biimpl x y = thm-nnf′ n (⇔-equiv₁ Γ⊢φ)
...  | nconj x y  = thm-nnf′ n (¬∧-to-¬∨¬ Γ⊢φ)
...  | ndisj x y  = thm-nnf′ n (¬∨-to-¬∧¬ Γ⊢φ)
...  | nneg x     = thm-nnf′ n (¬¬-equiv₁ Γ⊢φ)
...  | ntop       = ¬-elim Γ⊢φ ⊤-intro
...  | nbot       = ⊤-intro
...  | nimpl x y  = thm-nnf′ n (subst⊢¬ helper Γ⊢φ)
  where
    helper : Γ ⊢ y ∨ ¬ x ⇒ (x ⇒ y)
    helper = ⇒-intro (¬∨-to-⇒ (∨-comm (assume {Γ = Γ} (y ∨ ¬ x))))
...  | nbiim x y  =
  thm-nnf′ n
    (subst⊢¬
      (⇒-intro
        (⇔-equiv₂
          (assume {Γ = Γ} ((x ⇒ y) ∧ (y ⇒ x)))))
          Γ⊢φ)
...  | other .φ   = Γ⊢φ
thm-nnf′ {Γ} {φ} zero Γ⊢φ = Γ⊢φ

-- * ubsizetree function
-- This function pretends to be an upper bound for the size of the tree
-- associated to the recursion calls done by the nnf conversion algorithm.
-- To be precise about the number of calls in the recursion, we should use
-- the following definition instead of the one we are using:
-- ubsizetree .(x ⇒ y) | impl x y =
--     ubsizetree x + ubsizetree y + ubsizetree (¬ x) + ubsizetree (¬ y) + 3
-- Unfortunately, the termination checker complains about this computation.

ubsizetree : Prop → ℕ
ubsizetree φ with n-view φ
... | conj x y   = ubsizetree x + ubsizetree y + 1
... | disj x y   = ubsizetree x + ubsizetree y + 1
... | impl x y   = 2 * ubsizetree x + ubsizetree y + 1
... | biimpl x y = 2 * (ubsizetree x + ubsizetree y) + 3
... | nconj x y  = ubsizetree (¬ x) + ubsizetree (¬ y) + 1
... | ndisj x y  = ubsizetree (¬ x) + ubsizetree (¬ y) + 1
... | nneg x     = ubsizetree (¬ x) + 1
... | ntop       = 1
... | nbot       = 1
... | nimpl x y  = ubsizetree x + ubsizetree (¬ y) + 3
... | nbiim x y  =
  ubsizetree x + ubsizetree y + ubsizetree (¬ x) + ubsizetree (¬ y) + 8
... | other .φ   = 1

nnf : Prop → Prop
nnf φ = nnf′ (ubsizetree φ) φ

thm-nnf
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ nnf φ

thm-nnf {Γ} {φ} Γ⊢φ = thm-nnf′ (ubsizetree φ) Γ⊢φ

------------------------------------------------------------------------------
-- Disjunctive Normal Form (DNF)
------------------------------------------------------------------------------

dist-∧ : Prop → Prop
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


dist : Prop → Prop
dist φ with d-view φ
dist .(φ ∧ ψ) | conj φ ψ = dist-∧ (φ ∧ ψ)
dist .(φ ∨ ψ) | disj φ ψ = dist φ ∨ dist ψ
dist φ        | other .φ = φ

thm-dist
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ dist φ

thm-dist {Γ} {φ} Γ⊢φ with d-view φ
thm-dist {Γ} {φ ∧ ψ} Γ⊢φ∧ψ | conj .φ .ψ = thm-dist-∧ Γ⊢φ∧ψ
thm-dist {Γ} {φ ∨ ψ} Γ⊢φ∨ψ | disj .φ .ψ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ (dist ψ) (thm-dist (assume {Γ = Γ} φ)))
        (∨-intro₂ (dist φ) (thm-dist (assume {Γ = Γ} ψ)))))
    Γ⊢φ∨ψ
thm-dist {Γ} {φ} Γ⊢φ       | other .φ   = Γ⊢φ

dnf : Prop → Prop
dnf = dist ∘ nnf

thm-dnf
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ dnf φ

thm-dnf = thm-dist ∘ thm-nnf

------------------------------------------------------------------------------
-- Conjunctive Normal Forms (CNF)
------------------------------------------------------------------------------

dist-∨ : Prop → Prop
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

dist′ : Prop → Prop
dist′ φ with d-view φ
dist′ .(φ ∧ ψ) | conj φ ψ = dist′ φ ∧ dist′ ψ
dist′ .(φ ∨ ψ) | disj φ ψ = dist-∨ (φ ∨ ψ)
dist′ φ        | other .φ = φ

thm-dist′
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ dist′ φ

thm-dist′ {Γ} {φ} Γ⊢φ with d-view φ
thm-dist′ {Γ} {.(φ ∧ ψ)} Γ⊢φ∧ψ | conj φ ψ =
  ∧-intro (thm-dist′ (∧-proj₁ Γ⊢φ∧ψ)) (thm-dist′ (∧-proj₂ Γ⊢φ∧ψ))
thm-dist′ {Γ} {.(φ ∨ ψ)} Γ⊢φ∨ψ | disj φ ψ = thm-dist-∨ Γ⊢φ∨ψ
thm-dist′ {Γ} {.φ} Γ⊢φ         | other φ  = Γ⊢φ

cnf : Prop → Prop
cnf = dist′ ∘ nnf

thm-cnf
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ cnf φ

thm-cnf = thm-dist′ ∘ thm-nnf
