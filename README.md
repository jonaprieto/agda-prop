# Agda-Prop [![Build Status](https://travis-ci.org/jonaprieto/agda-prop.svg?branch=master)](https://travis-ci.org/jonaprieto/agda-prop) [![DOI](https://zenodo.org/badge/84277944.svg)](https://zenodo.org/badge/latestdoi/84277944)

This is a library to work with Classical Propositional Logic based on a deep embedding.
It also contains a compilation of useful theorems with their natural deduction proofs,
and some properties ready to work with and some algorithms like nnf, cnf, among others.

<!-- TOC depthFrom:2 depthTo:6 withLinks:1 updateOnSave:1 orderedList:0 -->

- [Quick Start](#quick-start)
	- [Requirements](#requirements)
	- [Installation](#installation)
- [Library](#library)
	- [Theorems](#theorems)
	- [Examples](#examples)
	- [References](#references)
	- [Contributions](#contributions)

<!-- /TOC -->

## Quick Start

We define two data types, the formula data type `Prop` and the sequen or theroem
data type `_⊢_`, that dependend of a *list* of hypotesis and the conclusion,
a formula. The constructors are the following.

```agda
data Prop : Type where
  Var  : Fin n → Prop           -- Variables.
  ⊤    : Prop                   -- Top (truth).
  ⊥    : Prop                   -- Bottom (falsum).
  _∧_  : (φ ψ : Prop) → Prop    -- Conjunction.
  _∨_  : (φ ψ : Prop) → Prop    -- Disjunction.
  _⇒_  : (φ ψ : Prop) → Prop    -- Implication.
  _⇔_  : (φ ψ : Prop) → Prop    -- Biimplication.
  ¬_   : (φ : Prop) → Prop      -- Negation.
```

The theroems use the following inference rules:

```agda
data _⊢_ : (Γ : Ctxt)(φ : Prop) → Type where

-- Hyp.

  assume   : ∀ {Γ} → (φ : Prop)           → Γ , φ ⊢ φ

  axiom    : ∀ {Γ} → (φ : Prop)           → φ ∈ Γ
                                          → Γ ⊢ φ

  weaken   : ∀ {Γ} {φ} → (ψ : Prop)       → Γ ⊢ φ
                                          → Γ , ψ ⊢ φ

  weaken₂  : ∀ {Γ} {φ} → (ψ : Prop)       → Γ ⊢ φ
                                          → ψ ∷ Γ ⊢ φ
-- Top and Bottom.

  ⊤-intro  : ∀ {Γ}                        → Γ ⊢ ⊤

  ⊥-elim   : ∀ {Γ} → (φ : Prop)           → Γ ⊢ ⊥
                                          → Γ ⊢ φ
-- Negation.

  ¬-intro  : ∀ {Γ} {φ}                    → Γ , φ ⊢ ⊥
                                          → Γ ⊢ ¬ φ

  ¬-elim   : ∀ {Γ} {φ}                    → Γ ⊢ ¬ φ → Γ ⊢ φ
                                          → Γ ⊢ ⊥
-- Conjunction.

  ∧-intro  : ∀ {Γ} {φ ψ}                  → Γ ⊢ φ → Γ ⊢ ψ
                                          → Γ ⊢ φ ∧ ψ

  ∧-proj₁  : ∀ {Γ} {φ ψ}                  → Γ ⊢ φ ∧ ψ
                                          → Γ ⊢ φ

  ∧-proj₂  : ∀ {Γ} {φ ψ}                  → Γ ⊢ φ ∧ ψ
                                          → Γ ⊢ ψ
-- Disjunction.

  ∨-intro₁ : ∀ {Γ} {φ} → (ψ : Prop)       → Γ ⊢ φ
                                          → Γ ⊢ φ ∨ ψ

  ∨-intro₂ : ∀ {Γ} {ψ} → (φ : Prop)       → Γ ⊢ ψ
                                          → Γ ⊢ φ ∨ ψ

  ∨-elim  : ∀ {Γ} {φ ψ χ}                 → Γ , φ ⊢ χ
                                          → Γ , ψ ⊢ χ
                                          → Γ , φ ∨ ψ ⊢ χ
-- Implication.

  ⇒-intro  : ∀ {Γ} {φ ψ}                  → Γ , φ ⊢ ψ
                                          → Γ ⊢ φ ⇒ ψ

  ⇒-elim   : ∀ {Γ} {φ ψ}                  → Γ ⊢ φ ⇒ ψ → Γ ⊢ φ
                                          → Γ ⊢ ψ
-- Biconditional.

  ⇔-intro  : ∀ {Γ} {φ ψ}                  → Γ , φ ⊢ ψ
                                          → Γ , ψ ⊢ φ
                                          → Γ ⊢ φ ⇔ ψ

  ⇔-elim₁ : ∀ {Γ} {φ ψ}                  → Γ ⊢ φ → Γ ⊢ φ ⇔ ψ
                                          → Γ ⊢ ψ

  ⇔-elim₂ : ∀ {Γ} {φ ψ}                   → Γ ⊢ ψ → Γ ⊢ φ ⇔ ψ
                                          →  Γ ⊢ φ
```

### Requirements

Tested with:

* [Agda](https://github.com/agda/agda) version 2.5.2
* [Agda Standard Library](https://github.com/agda/agda-stdlib/) v0.13


## Library


### Theorems

The theorems have a name based on their main connective, their purpose or their source.
We added sub-indices for those theorems that differ a little with other one.

* [List of Theorems][theorems]
  * [Biimplication](BIIMPLICATION)
  * [Classical](CLASSICAL)
  * [Conjunction](CONJUNCTION)
  * [Disjunction](DISJUNCTION)
  * [Implication](IMPLICATION)
  * [Negation](NEGATION)
  * [Mixies](MIXIES)
  * [Weakening](WEAKENING)


[theorems]: https://github.com/jonaprieto/agda-prop/tree/master/src/Data/Prop/Theorems
[BIIMPLICATION]:https://raw.githubusercontent.com/jonaprieto/agda-prop/master/src/Data/Prop/Theorems/Biimplication.agda
[CLASSICAL]:https://raw.githubusercontent.com/jonaprieto/agda-prop/master/src/Data/Prop/Theorems/Classical.agda
[CONJUNCTION]:https://raw.githubusercontent.com/jonaprieto/agda-prop/master/src/Data/Prop/Theorems/Conjunction.agda
[DISJUNCTION]:https://raw.githubusercontent.com/jonaprieto/agda-prop/master/src/Data/Prop/Theorems/Disjunction.agda
[IMPLICATION]:https://raw.githubusercontent.com/jonaprieto/agda-prop/master/src/Data/Prop/Theorems/Implication.agda
[NEGATION]:https://raw.githubusercontent.com/jonaprieto/agda-prop/master/src/Data/Prop/Theorems/Negation.agda
[MIXIES]:https://raw.githubusercontent.com/jonaprieto/agda-prop/master/src/Data/Prop/Theorems/Mixies.agda
[WEAKENING]:https://raw.githubusercontent.com/jonaprieto/agda-prop/master/src/Data/Prop/Theorems/Weakening.agda


### Additional Theorems

* [Normal Forms][theorems]
  * [Negative Normal Form (NNF)](https://github.com/jonaprieto/agda-prop/blob/master/src/Data/Prop/NormalForms.agda#L120)
  * [Disjunctive Normal Form (DNF)](https://github.com/jonaprieto/agda-prop/blob/master/src/Data/Prop/NormalForms.agda#L201)
  * [Conjunctive Normal Form (CNF)](https://github.com/jonaprieto/agda-prop/blob/master/src/Data/Prop/NormalForms.agda#L261)


### Example


```agda
$ cat test/ex-andreas-abel.agda
open import Data.Prop 2 public
...

EM⇒Pierce
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ((φ ⇒ ψ) ⇒ φ) ⇒ φ

EM⇒Pierce {Γ}{φ}{ψ} =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (⇒-intro
          (weaken ((φ ⇒ ψ) ⇒ φ)
            (assume {Γ = Γ} φ)))
        (⇒-intro
          (⇒-elim
            (assume {Γ = Γ , ¬ φ} ((φ ⇒ ψ) ⇒ φ))
              (⇒-intro
                (⊥-elim
                  ψ
                  (¬-elim
                  (weaken φ
                    (weaken ((φ ⇒ ψ) ⇒ φ)
                      (assume {Γ = Γ} (¬ φ))))
                      (assume {Γ = Γ , ¬ φ , (φ ⇒ ψ) ⇒ φ} φ))))
            ))))
      PEM -- ∀ {Γ} {φ}  → Γ ⊢ φ ∨ ¬ φ

...

```

### References

- Cai, L., Kaposi, A., & Altenkirch, T. (2015)
Formalising the Completeness Theorem of Classical Propositional Logic in Agda.
Retrieved from https://akaposi.github.io/proplogic.pdf
