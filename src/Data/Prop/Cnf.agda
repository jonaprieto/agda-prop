------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Cnf Conversion.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.Cnf (n : ℕ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Data.Fin
open import Data.List

------------------------------------------------------------------------------

data Literal : Set where
  Var : Fin n → Literal
  ¬l_  : Literal → Literal

Clause : Set
Clause = List Literal

Cnf : Set
Cnf = List Clause

_∧cnf_ : (φ ψ : Cnf) → Cnf
φ ∧cnf ψ = φ ++ ψ

cnfVar_ : (l : Literal) → Cnf
cnfVar l = [ [ l ] ]

_∨cnf_ : (φ ψ : Cnf) → Cnf
[] ∨cnf ψ  = ψ
φ  ∨cnf [] = φ
cls ∨cnf (x ∷ ψ) = (cls ∨⋆ x) ∧cnf (cls ∨cnf ψ)
  where
    _∨⋆_ : Cnf → Clause → Cnf
    [] ∨⋆ [] = []
    [] ∨⋆ ψ  = [ ψ ]
    φ  ∨⋆ [] = φ
    xs ∨⋆ ys = concatMap (λ x → [ x ++ ys ]) xs 

¬cnf_ : (φ : Cnf) → Cnf
¬cnf φ = φ

_⇒cnf_ : (φ ψ : Cnf) → Cnf
φ ⇒cnf ψ = (¬cnf φ) ∨cnf ψ
