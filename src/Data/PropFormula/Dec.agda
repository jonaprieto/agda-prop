------------------------------------------------------------------------------
-- Agda-Prop Library.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.PropFormula.Dec ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Syntax n

open import Data.Bool.Base using  ( Bool; false; true; not; T )
open import Data.Fin       using  ( Fin; suc; zero )
open import Data.Empty     hiding (⊥)

open import Function       using  ( _$_; _∘_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; cong )

------------------------------------------------------------------------------

data ⊥₂ : Set where

⊥₂-elim : ∀ {Whatever : Set} → ⊥₂ → Whatever
⊥₂-elim ()

infix 3 ¬₂_

¬₂_ : Set → Set
¬₂ P = P → ⊥₂

-- Decidable relations.

data Dec (P : Set) : Set where
  yes : ( p :    P) → Dec P
  no  : (¬p : ¬₂ P) → Dec P

⌊_⌋ : {P : Set} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false

REL : Set → Set → Set₁
REL A B = A → B → Set

Decidable : {A : Set} {B : Set} → REL A B → Set
Decidable _∼_ = ∀ x y → Dec (x ∼ y)
