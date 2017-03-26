------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Dec.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.Dec ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n

open import Data.Bool.Base using  ( Bool; false; true; not; T )
open import Data.Fin       using  ( Fin; suc; zero )
open import Data.Empty     hiding (⊥)

open import Level
open import Function       using  ( _$_; _∘_ )

open import Relation.Binary.PropositionalEquality using ( _≡_; refl; cong )

------------------------------------------------------------------------------

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
