------------------------------------------------------------------------
-- Agda-Prop Library.
-- Dec.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module Data.Prop.Dec (n : ℕ) where

open import Data.Bool.Base using (Bool; false; true; not; T)
open import Data.Prop.Syntax n
open import Data.Fin
open import Data.Empty

open import Level
open import Function using (_$_ ; _∘_)


open import Relation.Binary.PropositionalEquality


data ⊥₂ : Set where


infix 3 ¬₂_

¬₂_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬₂ P = P → ⊥₂

-- Decidable relations.

data Dec {p} (P : Set p) : Set p where
  yes : ( p :    P) → Dec P
  no  : (¬p : ¬₂ P) → Dec P


⌊_⌋ : ∀ {p} {P : Set p} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false

REL : ∀ {a b} → Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ Level.suc ℓ)
REL A B ℓ = A → B → Set ℓ

Decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ → Set _
Decidable _∼_ = ∀ x y → Dec (x ∼ y)

suc-injective : ∀ {o} {m n : Fin o} → Fin.suc m ≡ Fin.suc n → m ≡ n
suc-injective refl = refl

_≟_ : {n : ℕ} → Decidable {A = Fin n} _≡_
zero  ≟ zero  = yes refl
zero  ≟ suc y = no λ()
suc x ≟ zero  = no λ()
suc x ≟ suc y with x ≟ y
... | yes x≡y = yes (cong Fin.suc x≡y)
... | no  x≢y = no (λ r → x≢y (suc-injective r))


var-injective : ∀ {x x₁} → Var x ≡ Var x₁ → x ≡ x₁
var-injective refl = refl

∧-injective₁ : ∀ {p p' q q'} → (p ∧ p') ≡ (q ∧ q') → p ≡ q
∧-injective₁ refl = refl

∧-injective₂ : ∀ {p p' q q'} → (p ∧ p') ≡ (q ∧ q') → p' ≡ q'
∧-injective₂ refl = refl

∨-injective₁ : ∀ {p p' q q'} → (p ∨ p') ≡ (q ∨ q') → p ≡ q
∨-injective₁ refl = refl

∨-injective₂ : ∀ {p p' q q'} → (p ∨ p') ≡ (q ∨ q') → p' ≡ q'
∨-injective₂ refl = refl

⇒-injective₁ : ∀ {p p' q q'} → (p ⇒ p') ≡ (q ⇒ q') → p ≡ q
⇒-injective₁ refl = refl

⇒-injective₂ : ∀ {p p' q q'} → (p ⇒ p') ≡ (q ⇒ q') → p' ≡ q'
⇒-injective₂ refl = refl

⇔-injective₁ : ∀ {p p' q q'} → (p ⇔ p') ≡ (q ⇔ q') → p ≡ q
⇔-injective₁ refl = refl

⇔-injective₂ : ∀ {p p' q q'} → (p ⇔ p') ≡ (q ⇔ q') → p' ≡ q'
⇔-injective₂ refl = refl


eq : (φ ψ : Prop) → Dec (φ ≡ ψ)

eq (Var x) (Var x₁) with x ≟ x₁
... | yes refl = yes refl
... | no x≢x₁  = no (λ r → x≢x₁ (var-injective r))
eq (Var x) ⊤        = no (λ())
eq (Var x) ⊥        = no (λ())
eq (Var x) (ψ ∧ ψ₁) = no (λ())
eq (Var x) (ψ ∨ ψ₁) = no (λ())
eq (Var x) (ψ ⇒ ψ₁) = no (λ())
eq (Var x) (ψ ⇔ ψ₁) = no (λ())
eq (Var x) (¬ ψ)    = no (λ())

eq ⊤ (Var x)        = no λ()
eq ⊤ ⊤              = yes refl
eq ⊤ ⊥              = no λ()
eq ⊤ (ψ ∧ ψ₁)       = no (λ())
eq ⊤ (ψ ∨ ψ₁)       = no (λ())
eq ⊤ (ψ ⇒ ψ₁)       = no (λ())
eq ⊤ (ψ ⇔ ψ₁)       = no (λ())
eq ⊤ (¬ ψ)           = no (λ())

eq (φ ∧ φ₁) (Var x)  = no (λ())
eq (φ ∧ φ₁) ⊤        = no (λ())
eq (φ ∧ φ₁) ⊥        = no (λ())
eq (φ ∧ φ₁) (ψ ∧ ψ₁) with eq φ ψ | eq φ₁ ψ₁
eq (φ ∧ φ₁) (ψ ∧ ψ₁) | yes refl | yes refl = yes refl
eq (φ ∧ φ₁) (ψ ∧ ψ₁) | yes _    | no φ₁≢ψ₁ = no (λ r → φ₁≢ψ₁ (∧-injective₂ r))
eq (φ ∧ φ₁) (ψ ∧ ψ₁) | no φ≢ψ   | y        = no (λ r → φ≢ψ (∧-injective₁ r))
eq (φ ∧ φ₁) (ψ ∨ ψ₁) = no λ()
eq (φ ∧ φ₁) (ψ ⇒ ψ₁) = no λ()
eq (φ ∧ φ₁) (ψ ⇔ ψ₁) = no λ()
eq (φ ∧ φ₁) (¬ ψ)    = no λ()

eq (φ ∨ φ₁) (Var x)  = no λ()
eq (φ ∨ φ₁) ⊤        = no λ()
eq (φ ∨ φ₁) ⊥        = no λ()
eq (φ ∨ φ₁) (ψ ∧ ψ₁) = no λ()
eq (φ ∨ φ₁) (ψ ∨ ψ₁) = {!!}
eq (φ ∨ φ₁) (ψ ⇒ ψ₁) = {!!}
eq (φ ∨ φ₁) (ψ ⇔ ψ₁) = {!!}
eq (φ ∨ φ₁) (¬ ψ)    = {!!}
eq (φ ⇒ φ₁) ψ        = {!!}
eq (φ ⇔ φ₁) ψ        = {!!}
eq (φ) ψ             = {!!}

