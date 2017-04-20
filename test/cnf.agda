------------------------------------------------------------------------------
-- test conjunctive normal forms.
------------------------------------------------------------------------------

open import Data.Prop 3 public

open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl)

------------------------------------------------------------------------------

-- Variables.

p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

r : Prop
r = Var (# 2)

φ : Prop
φ = (p ∧ q) ∨ (¬ r)

cnfφ : Prop
cnfφ = (p ∨ ¬ r) ∧ (q ∨ ¬ r)

p1 : cnf φ ≡ cnfφ
p1 = refl

ψ : Prop
ψ = (¬ r) ∨ (p ∧ q)

cnfψ : Prop
cnfψ = (¬ r ∨ p) ∧ (¬ r ∨ q)

p2 : cnf ψ ≡ cnfψ
p2 = refl

ω : Prop
ω = cnf (¬ cnfψ)

cnfω : Prop
cnfω = r ∧ (¬ p ∧ (r ∧ ¬ q))

p3 : ω ≡ cnfω
p3 = refl
