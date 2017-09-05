module nform where

open import Data.PropFormula (3) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

p : PropFormula
p = Var (# 0)

q : PropFormula
q = Var (# 1)

r : PropFormula
r = Var (# 2)

φ : PropFormula
φ = ¬ ((p ∧ (p ⇒ q)) ⇒ q) -- (p ∧ q) ∨ (¬ r)

cnfφ : PropFormula
cnfφ = ¬ q ∧ (p ∧ (¬ p ∨ q))

postulate
 p1 : ∅ ⊢ φ

p2 : ∅ ⊢ cnfφ
p2 = thm-cnf p1 -- thm-cnf p1

{-
p3 : cnf φ ≡ cnfφ
p3 = refl

ψ : PropFormula
ψ = (¬ r) ∨ (p ∧ q)

cnfψ : PropFormula
cnfψ = (¬ r ∨ p) ∧ (¬ r ∨ q)

p5 : cnf ψ ≡ cnfψ
p5 = refl
-}

to5   = (¬ p) ∨ ((¬ q) ∨ r)
from5 = (¬ p) ∨ (r ∨ ((¬ q) ∧ p))

test : ⌊ eq (cnf from5) to5 ⌋ ≡ false
test = refl
