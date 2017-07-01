module bags where

open import Data.Prop.Syntax 4
open import Data.Prop.SyntaxExperiment 4 public
open import Data.Fin using (suc; zero; #_)
open import Relation.Binary.PropositionalEquality using (_≡_)

p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

pq : Prop
pq = p ∧ q

qp : Prop
qp = q ∧ p

listpq : List Prop
listpq = toList pq

listqp : List Prop
listqp = toList qp
