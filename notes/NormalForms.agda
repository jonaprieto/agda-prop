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

data Literal : Set where
  Var  : Fin n   → Literal
  ¬l_  : Literal → Literal

Clause : Set
Clause = List Literal

------------------------------------------------------------------------------
-- Conjunctive Normal Form (CNF)
------------------------------------------------------------------------------

Cnf : Set
Cnf = List Clause

varCnf_ : Literal → Cnf
varCnf l = [ [ l ] ]

_∧Cnf_ : (φ ψ : Cnf) → Cnf
φ ∧Cnf ψ = φ ++ ψ

_∨Cnf_ : (φ ψ : Cnf) → Cnf
[]  ∨Cnf ψ       = ψ
φ   ∨Cnf []      = []
cls ∨Cnf (x ∷ ψ) = (cls ∨⋆ x) ∧Cnf (cls ∨Cnf ψ)
  where
    _∨⋆_ : Cnf → Clause → Cnf
    xs ∨⋆ ys = concatMap (λ x → [ x ++ ys ]) xs

¬Cnf₀_ : Literal → Literal
¬Cnf₀ Var x    = ¬l Var x
¬Cnf₀ (¬l lit) = lit

¬Cnf₁ : Clause → Cnf
¬Cnf₁ []  = []  -- ¬ ⊥ → ⊤
¬Cnf₁ cls = map (λ lit → [ ¬Cnf₀ lit ]) cls

¬Cnf : Cnf → Cnf
¬Cnf [] = [ [] ]
¬Cnf fm = concatMap (λ cl → ¬Cnf₁ cl) fm

_⇒Cnf_ : (φ ψ : Cnf) → Cnf
φ ⇒Cnf ψ = (¬Cnf φ) ∨Cnf ψ

_⇔Cnf_ : (φ ψ : Cnf) → Cnf
φ ⇔Cnf ψ = (φ ⇒Cnf ψ) ∧Cnf (ψ ⇒Cnf φ)

toCnf : Prop → Cnf
toCnf (Var x) = varCnf Var x
toCnf ⊤       = []
toCnf ⊥       = [ [] ]
toCnf (φ ∧ ψ) = toCnf φ ∧Cnf toCnf ψ
toCnf (φ ∨ ψ) = toCnf φ ∨Cnf toCnf ψ
toCnf (φ ⇒ ψ) = toCnf φ ⇒Cnf toCnf ψ
toCnf (φ ⇔ ψ) = toCnf φ ⇔Cnf toCnf ψ
toCnf (¬ φ)   = ¬Cnf (toCnf φ)

toPropLiteral : Literal → Prop
toPropLiteral (Var x)  = Var x
toPropLiteral (¬l lit) = ¬ toPropLiteral lit

toPropClause : Clause → Prop
toPropClause []       = ⊥
toPropClause (l ∷ []) = toPropLiteral l
toPropClause (l ∷ ls) = toPropLiteral l ∨ toPropClause ls

toProp : Cnf → Prop
toProp []         = ⊤
toProp (fm ∷ [] ) = toPropClause fm
toProp (fm ∷ fms) = toPropClause fm ∧ toProp fms

cnf : Prop → Prop
cnf = toProp ∘ toCnf

-- ------------------------------------------------------------------------------
-- -- test conjunctive normal forms.
-- ------------------------------------------------------------------------------

-- open import Data.Prop 3 public
-- open import Data.Prop.Properties 3 using ( subst )
-- open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl; sym)

-- -- Variables.

-- p : Prop
-- p = Var (# 0)

-- q : Prop
-- q = Var (# 1)

-- r : Prop
-- r = Var (# 2)

-- φ : Prop
-- φ = (p ∧ q) ∨ (¬ r)

-- cnfφ : Prop
-- cnfφ = (p ∨ ¬ r) ∧ (q ∨ ¬ r)

-- p1 : cnf φ ≡ cnfφ
-- p1 = refl

-- ψ : Prop
-- ψ = (¬ r) ∨ (p ∧ q)

-- cnfψ : Prop
-- cnfψ = (¬ r ∨ p) ∧ (¬ r ∨ q)

-- p2 : cnf ψ ≡ cnfψ
-- p2 = refl

-- ω : Prop
-- ω = cnf (¬ cnfψ)

-- cnfω : Prop
-- cnfω = r ∧ (¬ p ∧ (r ∧ ¬ q))

-- p3 : ω ≡ cnfω
-- p3 = refl