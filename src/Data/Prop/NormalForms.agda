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

open import Relation.Nullary using (yes; no)
open import Data.Prop.Theorems n

open import Function using ( _∘_; _$_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; sym )

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Negation Normal Form (NNF)
------------------------------------------------------------------------------

data nView : Prop  → Set where
  conj   : (x y : Prop) → nView (x ∧ y)
  disj   : (x y : Prop) → nView (x ∨ y)
  impl   : (x y : Prop) → nView (x ⇒ y)
  biimpl : (x y : Prop) → nView (x ⇔ y)
  nconj  : (x y : Prop) → nView (¬ (x ∧ y))
  ndisj  : (x y : Prop) → nView (¬ (x ∨ y))
  nneg   : (x : Prop)   → nView (¬ ¬ x)
  ntop   : nView (¬ ⊤)
  nbot   : nView (¬ ⊥)
  nimpl  : (x y : Prop) → nView (¬ (x ⇒ y))
  nbiim  : (x y : Prop) → nView (¬ (x ⇔ y))
  other  : (x : Prop)   → nView x

n-view : (φ : Prop) → nView φ
n-view (φ ∧ ψ)      = conj _ _
n-view (φ ∨ ψ)      = disj _ _
n-view (φ ⇒ ψ)      = impl _ _
n-view (φ ⇔ ψ)      = biimpl _ _
n-view (¬ ⊤)        = ntop
n-view (¬ ⊥)        = nbot
n-view (¬ (φ ∧ φ₁)) = nconj _ _
n-view (¬ (φ ∨ φ₁)) = ndisj _ _
n-view (¬ (φ ⇒ φ₁)) = nimpl _ _
n-view (¬ (φ ⇔ φ₁)) = nbiim _ _
n-view (¬ (¬ φ))    = nneg _
n-view φ            = other _

nnf′ : ℕ → Prop → Prop
nnf′ n φ with n-view φ
nnf′ (suc n) .(x ∧ y)     | conj x y   = nnf′ n x ∧ nnf′ n y
nnf′ (suc n) .(x ∨ y)     | disj x y   = nnf′ n x ∨ nnf′ n y
nnf′ (suc n) .(x ⇒ y)     | impl x y   = nnf′ n ((¬ x) ∨ y)
nnf′ (suc n) .(x ⇔ y)     | biimpl x y = nnf′ n ((x ⇒ y) ∧ (y ⇒ x))
nnf′ (suc n) .(¬ (x ∧ y)) | nconj x y  = nnf′ n ((¬ x) ∨ (¬ y))
nnf′ (suc n) .(¬ (x ∨ y)) | ndisj x y  = nnf′ n ((¬ x) ∧ (¬ y))
nnf′ (suc n) .(¬ (¬ x))   | nneg x     = nnf′ n x
nnf′ (suc n) .(¬ ⊤)       | ntop       = ⊥
nnf′ (suc n) .(¬ ⊥)       | nbot       = ⊤
nnf′ (suc n) .(¬ (x ⇒ y)) | nimpl x y  = nnf′ n (¬ ((¬ x) ∨ y))
nnf′ (suc n) .(¬ (x ⇔ y)) | nbiim x y  = nnf′ n (¬ ((x ⇒ y) ∧ (y ⇒ x)))
nnf′ (suc n) φ            | other .φ   = φ
nnf′ zero φ               | _          = φ


thm-nnf′
  : ∀ {Γ} {φ}
  → (n : ℕ)
  → Γ ⊢ φ
  → Γ ⊢ nnf′ n φ

thm-nnf′ {Γ} {φ} n₁ Γ⊢φ with n-view φ
thm-nnf′ {Γ} {.(x ∧ y)} (suc n) Γ⊢x∧y | conj x y =
  ∧-intro (thm-nnf′ n (∧-proj₁ Γ⊢x∧y)) (thm-nnf′ n (∧-proj₂ Γ⊢x∧y))
thm-nnf′ {Γ} {.(x ∨ y)} (suc n) Γ⊢x∨y | disj x y =
  (⇒-elim
    (⇒-intro
     (∨-elim {Γ = Γ}
       (∨-intro₁
         (nnf′ n y)
         (thm-nnf′ n (assume {Γ = Γ} x)))
       (∨-intro₂
         (nnf′ n x)
         (thm-nnf′ n (assume {Γ = Γ} y)))))
      Γ⊢x∨y)
thm-nnf′ {Γ} {.(x ⇒ y)} (suc n) Γ⊢x⇒y       | impl x y   = thm-nnf′ n (⇒-to-¬∨ Γ⊢x⇒y)
thm-nnf′ {Γ} {.(x ⇔ y)} (suc n) Γ⊢x⇔y      | biimpl x y = thm-nnf′ n (⇔-equiv₁ Γ⊢x⇔y)
thm-nnf′ {Γ} {.(¬ (x ∧ y))} (suc n) Γ⊢¬⟨x∧y⟩ | nconj x y  = thm-nnf′ n (¬∧-to-¬∨¬ Γ⊢¬⟨x∧y⟩)
thm-nnf′ {Γ} {.(¬ (x ∨ y))} (suc n) Γ⊢¬⟨x∨y⟩ | ndisj x y  = thm-nnf′ n (¬∨-to-¬∧¬ Γ⊢¬⟨x∨y⟩)
thm-nnf′ {Γ} {.(¬ (¬ x))} (suc n) Γ⊢¬¬φ     | nneg x     = thm-nnf′ n (¬¬-equiv₁ Γ⊢¬¬φ)
thm-nnf′ {Γ} {.(¬ ⊤)} (suc n) Γ⊢¬⊤          | ntop       = ¬-elim Γ⊢¬⊤ ⊤-intro
thm-nnf′ {Γ} {.(¬ ⊥)} (suc n) Γ⊢¬⊥          | nbot       = ⊤-intro
thm-nnf′ {Γ} {.(¬ (x ⇒ y))} (suc n) Γ⊢¬x⇒y  | nimpl x y  =
  thm-nnf′ n (subst⊢¬ helper Γ⊢¬x⇒y)
  where
    helper : Γ ⊢ ¬ x ∨ y ⇒ (x ⇒ y)
    helper = ⇒-intro (¬∨-to-⇒ (assume {Γ = Γ} (¬ x ∨ y)))
thm-nnf′ {Γ} {.(¬ (x ⇔ y))} (suc n) Γ⊢¬x⇔y    | nbiim x y =
  thm-nnf′ n
    (subst⊢¬
      (⇒-intro
        (⇔-equiv₂
          (assume {Γ = Γ} ((x ⇒ y) ∧ (y ⇒ x)))))
          Γ⊢¬x⇔y)
thm-nnf′ {Γ} {.x} (suc n) Γ⊢φ               | other x    = Γ⊢φ
thm-nnf′ {Γ} {.(x ∧ y)} zero Γ⊢φ            | conj x y   = Γ⊢φ
thm-nnf′ {Γ} {.(x ∨ y)} zero Γ⊢φ            | disj x y   = Γ⊢φ
thm-nnf′ {Γ} {.(x ⇒ y)} zero Γ⊢φ            | impl x y   = Γ⊢φ
thm-nnf′ {Γ} {.(x ⇔ y)} zero Γ⊢φ            | biimpl x y = Γ⊢φ
thm-nnf′ {Γ} {.(¬ (x ∧ y))} zero Γ⊢φ        | nconj x y  = Γ⊢φ
thm-nnf′ {Γ} {.(¬ (x ∨ y))} zero Γ⊢φ        | ndisj x y  = Γ⊢φ
thm-nnf′ {Γ} {.(¬ (¬ x))} zero Γ⊢φ          | nneg x     = Γ⊢φ
thm-nnf′ {Γ} {.(¬ ⊤)} zero Γ⊢φ              | ntop       = Γ⊢φ
thm-nnf′ {Γ} {.(¬ ⊥)} zero Γ⊢φ              | nbot       = Γ⊢φ
thm-nnf′ {Γ} {.(¬ (x ⇒ y))} zero Γ⊢φ        | nimpl x y  = Γ⊢φ
thm-nnf′ {Γ} {.(¬ (x ⇔ y))} zero Γ⊢φ        | nbiim x y  = Γ⊢φ
thm-nnf′ {Γ} {.x} zero Γ⊢φ                  | other x    = Γ⊢φ

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
ubsizetree .(x ∧ y)     | conj x y   = ubsizetree x + ubsizetree y + 1
ubsizetree .(x ∨ y)     | disj x y   = ubsizetree x + ubsizetree y + 1
ubsizetree .(x ⇒ y)     | impl x y   = 2 * ubsizetree x + ubsizetree y + 1
ubsizetree .(x ⇔ y)     | biimpl x y = 2 * (ubsizetree x + ubsizetree y) + 3
ubsizetree .(¬ (x ∧ y)) | nconj x y  = ubsizetree (¬ x) + ubsizetree (¬ y) + 1
ubsizetree .(¬ (x ∨ y)) | ndisj x y  = ubsizetree (¬ x) + ubsizetree (¬ y) + 1
ubsizetree .(¬ (¬ x))   | nneg x     = ubsizetree (¬ x) + 1
ubsizetree .(¬ ⊤)       | ntop       = 1
ubsizetree .(¬ ⊥)       | nbot       = 1
ubsizetree .(¬ (x ⇒ y)) | nimpl x y  = ubsizetree x + ubsizetree (¬ y) + 3
ubsizetree .(¬ (x ⇔ y)) | nbiim x y  =
  ubsizetree x + ubsizetree y + ubsizetree (¬ x) + ubsizetree (¬ y) + 8
ubsizetree φ            | other .φ   = 1

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

data dView : Prop → Set where
  conj  : (φ ψ : Prop) → dView (φ ∧ ψ)
  disj  : (φ ψ : Prop) → dView (φ ∨ ψ)
  other : (φ : Prop)   → dView φ

d-view : (φ : Prop) → dView φ
d-view (φ ∧ ψ) = conj _ _
d-view (φ ∨ ψ) = disj _ _
d-view φ       = other _

data dViewAux : Prop → Set where
  case₁ : (φ ψ ω : Prop) → dViewAux ((φ ∨ ψ) ∧ ω)
  case₂ : (φ ψ ω : Prop) → dViewAux (φ ∧ (ψ ∨ ω))
  other : (φ : Prop)     → dViewAux φ

d-view-aux : (φ : Prop) → dViewAux φ
d-view-aux ((φ ∨ ψ) ∧ ω) = case₁ _ _ _
d-view-aux (φ ∧ (ψ ∨ ω)) = case₂ _ _ _
d-view-aux φ             = other _

dist-∧ : Prop → Prop
dist-∧ φ with d-view-aux φ
dist-∧ .((φ ∨ ψ) ∧ ω) | case₁ φ ψ ω = dist-∧ (φ ∧ ω) ∨ dist-∧ (ψ ∧ ω)
dist-∧ .(φ ∧ (ψ ∨ ω)) | case₂ φ ψ ω = dist-∧ (φ ∧ ψ) ∨ dist-∧ (φ ∧ ω)
dist-∧ φ              | other .φ    = φ

thm-dist-∧
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ dist-∧ φ

thm-dist-∧ {Γ} {φ} Γ⊢φ with d-view-aux φ
thm-dist-∧ {Γ} {.((φ ∨ ψ) ∧ ω)} Γ⊢⟨φ∨ψ⟩∧ω | case₁ φ ψ ω =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ (dist-∧ (ψ ∧ ω))
          (thm-dist-∧
            (∧-intro (assume {Γ = Γ} φ) (weaken φ (∧-proj₂ Γ⊢⟨φ∨ψ⟩∧ω)))))
        (∨-intro₂ (dist-∧ (φ ∧ ω))
          (thm-dist-∧
            (∧-intro (assume {Γ = Γ} ψ) (weaken ψ (∧-proj₂ Γ⊢⟨φ∨ψ⟩∧ω)))))))
     (∧-proj₁ Γ⊢⟨φ∨ψ⟩∧ω)
thm-dist-∧ {Γ} {.(φ ∧ (ψ ∨ ω))} Γ⊢φ∧⟨ψ∨ω⟩ | case₂ φ ψ ω =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ (dist-∧ (φ ∧ ω))
          (thm-dist-∧
            (∧-intro (weaken ψ (∧-proj₁ Γ⊢φ∧⟨ψ∨ω⟩)) (assume {Γ = Γ} ψ))))
        (∨-intro₂ (dist-∧ (φ ∧ ψ))
          (thm-dist-∧
            (∧-intro (weaken ω (∧-proj₁ Γ⊢φ∧⟨ψ∨ω⟩)) (assume {Γ = Γ} ω))))))
    (∧-proj₂ Γ⊢φ∧⟨ψ∨ω⟩)
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
