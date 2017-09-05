------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Useful views.
------------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module Data.PropFormula.Views (n : ℕ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Syntax n

------------------------------------------------------------------------------

data nView : PropFormula  → Set where
  conj   : (φ₁ φ₂ : PropFormula) → nView (φ₁ ∧ φ₂)
  disj   : (φ₁ φ₂ : PropFormula) → nView (φ₁ ∨ φ₂)
  impl   : (φ₁ φ₂ : PropFormula) → nView (φ₁ ⇒ φ₂)
  biimpl : (φ₁ φ₂ : PropFormula) → nView (φ₁ ⇔ φ₂)
  nconj  : (φ₁ φ₂ : PropFormula) → nView (¬ (φ₁ ∧ φ₂))
  ndisj  : (φ₁ φ₂ : PropFormula) → nView (¬ (φ₁ ∨ φ₂))
  nneg   : (φ₁ : PropFormula)    → nView (¬ ¬ φ₁)
  ntop   : nView (¬ ⊤)
  nbot   : nView (¬ ⊥)
  nimpl  : (φ₁ φ₂ : PropFormula) → nView (¬ (φ₁ ⇒ φ₂))
  nbiim  : (φ₁ φ₂ : PropFormula) → nView (¬ (φ₁ ⇔ φ₂))
  other  : (φ₁ : PropFormula)    → nView φ₁

n-view : (φ : PropFormula) → nView φ
n-view (φ₁ ∧ φ₂)     = conj _ _
n-view (φ₁ ∨ φ₂)     = disj _ _
n-view (φ₁ ⇒ φ₂)     = impl _ _
n-view (φ₁ ⇔ φ₂)     = biimpl _ _
n-view (¬ ⊤)         = ntop
n-view (¬ ⊥)         = nbot
n-view (¬ (φ₁ ∧ φ₂)) = nconj _ _
n-view (¬ (φ₁ ∨ φ₂)) = ndisj _ _
n-view (¬ (φ₁ ⇒ φ₂)) = nimpl _ _
n-view (¬ (φ₁ ⇔ φ₂)) = nbiim _ _
n-view (¬ (¬ φ₁))    = nneg _
n-view φ₁            = other _

data ConjView : PropFormula → Set where
  conj  : (φ₁ φ₂ : PropFormula) → ConjView (φ₁ ∧ φ₂)
  other : (φ : PropFormula)     → ConjView φ

conj-view : (φ : PropFormula) → ConjView φ
conj-view (φ₁ ∧ φ₂) = conj _ _
conj-view φ         = other _

data DisjView : PropFormula → Set where
  disj  : (φ₁ φ₂ : PropFormula) → DisjView (φ₁ ∨ φ₂)
  other : (φ : PropFormula)     → DisjView φ

disj-view : (φ : PropFormula) → DisjView φ
disj-view (φ₁ ∨ φ₂) = disj _ _
disj-view φ         = other _


data dView : PropFormula → Set where
  conj  : (φ₁ φ₂ : PropFormula) → dView (φ₁ ∧ φ₂)
  disj  : (φ₁ φ₂ : PropFormula) → dView (φ₁ ∨ φ₂)
  other : (φ : PropFormula)     → dView φ

d-view : (φ : PropFormula) → dView φ
d-view (φ₁ ∧ φ₂) = conj _ _
d-view (φ₁ ∨ φ₂) = disj _ _
d-view φ         = other _

data dViewAux : PropFormula → Set where
  case₁ : (φ₁ φ₂ φ₃ : PropFormula) → dViewAux ((φ₁ ∨ φ₂) ∧ φ₃)
  case₂ : (φ₁ φ₂ φ₃ : PropFormula) → dViewAux (φ₁ ∧ (φ₂ ∨ φ₃))
  other : (φ : PropFormula)        → dViewAux φ

d-view-aux : (φ : PropFormula) → dViewAux φ
d-view-aux ((φ₁ ∨ φ₂) ∧ φ₃) = case₁ _ _ _
d-view-aux (φ₁ ∧ (φ₂ ∨ φ₃)) = case₂ _ _ _
d-view-aux φ                = other _

data cViewAux : PropFormula → Set where
  case₁ : (φ₁ φ₂ φ₃ : PropFormula) → cViewAux ((φ₁ ∧ φ₂) ∨ φ₃)
  case₂ : (φ₁ φ₂ φ₃ : PropFormula) → cViewAux (φ₁ ∨ (φ₂ ∧ φ₃))
  other : (φ : PropFormula)        → cViewAux φ

c-view-aux : (φ : PropFormula) → cViewAux φ
c-view-aux ((φ ∧ ψ) ∨ φ₃) = case₁ _ _ _
c-view-aux (φ ∨ (ψ ∧ φ₃)) = case₂ _ _ _
c-view-aux φ              = other _


data ImplView : PropFormula → Set where
  impl  : (φ₁ φ₂ : PropFormula) → ImplView (φ₁ ⇒ φ₂)
  other : (φ : PropFormula)     → ImplView φ

impl-view : (φ : PropFormula) → ImplView φ
impl-view (φ₁ ⇒ φ₂) = impl _ _
impl-view φ         = other _


data NegView : PropFormula → Set where
  neg : (φ : PropFormula) → NegView (¬ φ)
  pos : (φ : PropFormula) → NegView φ

neg-view : (φ : PropFormula) → NegView φ
neg-view (¬ φ) = neg _
neg-view φ     = pos _

