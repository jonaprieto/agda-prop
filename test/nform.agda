module nform where

open import Data.Prop (3) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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

postulate
 p1 : ∅ ⊢ φ

p2 : ∅ ⊢ cnfφ
p2 = thm-cnf p1


p3 : cnf φ ≡ cnfφ
p3 = refl

ψ : Prop
ψ = (¬ r) ∨ (p ∧ q)

cnfψ : Prop
cnfψ = (¬ r ∨ p) ∧ (¬ r ∨ q)

p5 : cnf ψ ≡ cnfψ
p5 = refl
