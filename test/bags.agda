module bags where

open import Data.PropFormula.Syntax 4
open import Data.PropFormula.SyntaxExperiment 4 public
open import Data.Fin using (suc; zero; #_)
open import Relation.Binary.PropositionalEquality using (_≡_)

p : PropFormula
p = Var (# 0)

q : PropFormula
q = Var (# 1)

pq : PropFormula
pq = p ∧ q

qp : PropFormula
qp = q ∧ p

listpq : List PropFormula
listpq = toList pq

listqp : List PropFormula
listqp = toList qp
