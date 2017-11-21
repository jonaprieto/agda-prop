# Agda-Prop [![Build Status](https://travis-ci.org/jonaprieto/agda-prop.svg?branch=master)](https://travis-ci.org/jonaprieto/agda-prop) [![DOI](https://zenodo.org/badge/84277944.svg)](https://zenodo.org/badge/latestdoi/84277944)

This is a library to work with Classical Propositional Logic based on a deep embedding.
It also contains a compilation of useful theorems with their natural deduction proofs,
and some properties ready to work with and some algorithms like NNF, CNF, among others.

<!-- TOC depthFrom:2 depthTo:6 withLinks:1 updateOnSave:1 orderedList:0 -->

- [Quick Start](#quick-start)
- [Library](#library)
	- [Theorems](#theorems)
	- [Examples](#examples)
	- [References](#references)

<!-- /TOC -->

## Quick Start

We define two data types, the formula data type `Prop` and the theorem
data type `_⊢_`, that depended of a *list* of hypothesis and the conclusion,
a formula. The constructors are the following.

```agda
data PropFormula : Type where
  Var  : Fin n → PropFormula           -- Variables.
  ⊤    : PropFormula                   -- Top (truth).
  ⊥    : PropFormula                   -- Bottom (falsum).
  _∧_  : (φ ψ : PropFormula) → Prop    -- Conjunction.
  _∨_  : (φ ψ : PropFormula) → Prop    -- Disjunction.
  _⊃_  : (φ ψ : PropFormula) → Prop    -- Implication.
  _⇔_  : (φ ψ : PropFormula) → Prop    -- Biimplication.
  ¬_   : (φ : PropFormula)   → Prop    -- Negation.
```

The theorems use the following inference rules:

```agda
data _⊢_ : (Γ : Ctxt)(φ : PropFormula) → Set where

-- Hyp.

  assume   : ∀ {Γ} → (φ : PropFormula)      → Γ , φ ⊢ φ

  axiom    : ∀ {Γ} → (φ : PropFormula)      → φ ∈ Γ
                                            → Γ ⊢ φ

  weaken   : ∀ {Γ} {φ} → (ψ : PropFormula)  → Γ ⊢ φ
                                            → Γ , ψ ⊢ φ

  weaken₂   : ∀ {Γ} {φ} → (ψ : PropFormula) → Γ ⊢ φ
                                            → ψ ∷ Γ ⊢ φ
-- Top and Bottom.

  ⊤-intro  : ∀ {Γ}                          → Γ ⊢ ⊤

  ⊥-elim   : ∀ {Γ} → (φ : PropFormula)      → Γ ⊢ ⊥
                                            → Γ ⊢ φ
-- Negation.

  ¬-intro  : ∀ {Γ} {φ}                      → Γ , φ ⊢ ⊥
                                            → Γ ⊢ ¬ φ

  ¬-elim   : ∀ {Γ} {φ}                      → Γ ⊢ ¬ φ → Γ ⊢ φ
                                            → Γ ⊢ ⊥
-- Conjunction.

  ∧-intro  : ∀ {Γ} {φ ψ}                    → Γ ⊢ φ → Γ ⊢ ψ
                                            → Γ ⊢ φ ∧ ψ

  ∧-proj₁  : ∀ {Γ} {φ ψ}                    → Γ ⊢ φ ∧ ψ
                                            → Γ ⊢ φ

  ∧-proj₂  : ∀ {Γ} {φ ψ}                    → Γ ⊢ φ ∧ ψ
                                            → Γ ⊢ ψ
-- Disjunction.

  ∨-intro₁ : ∀ {Γ} {φ} → (ψ : PropFormula)  → Γ ⊢ φ
                                            → Γ ⊢ φ ∨ ψ

  ∨-intro₂ : ∀ {Γ} {ψ} → (φ : PropFormula)  → Γ ⊢ ψ
                                            → Γ ⊢ φ ∨ ψ

  ∨-elim  : ∀ {Γ} {φ ψ χ}                   → Γ , φ ⊢ χ
                                            → Γ , ψ ⊢ χ
                                            → Γ , φ ∨ ψ ⊢ χ
-- Implication.

  ⊃-intro  : ∀ {Γ} {φ ψ}                    → Γ , φ ⊢ ψ
                                            → Γ ⊢ φ ⊃ ψ

  ⊃-elim   : ∀ {Γ} {φ ψ}                    → Γ ⊢ φ ⊃ ψ → Γ ⊢ φ
                                            → Γ ⊢ ψ
-- Biconditional.

  ⇔-intro  : ∀ {Γ} {φ ψ}                    → Γ , φ ⊢ ψ
                                            → Γ , ψ ⊢ φ
                                            → Γ ⊢ φ ⇔ ψ

  ⇔-elim₁ : ∀ {Γ} {φ ψ}                     → Γ ⊢ φ → Γ ⊢ φ ⇔ ψ
                                            → Γ ⊢ ψ

  ⇔-elim₂ : ∀ {Γ} {φ ψ}                     → Γ ⊢ ψ → Γ ⊢ φ ⇔ ψ
                                            → Γ ⊢ φ
```

### Requirements

Tested with:

* [Agda](https://github.com/agda/agda) version 2.5.2
* [Agda Standard Library](https://github.com/agda/agda-stdlib/) v0.13


## Library

We have a list of [theorems][theorems] for each connective and a mix of
them. Their names are based on their main connective, their purpose or
their source.  We added sub-indices for those theorems that differ a little with other one. If you need an specific theorem that you think
we should include, open an issue.

[theorems]: https://github.com/jonaprieto/agda-prop/tree/master/src/Data/Prop/Theorems

### Additional Theorems

* [Normal Forms][theorems]
  * [Negative Normal Form (NNF)](https://github.com/jonaprieto/agda-prop/blob/master/src/Data/Prop/NormalForms.agda#L120)
  * [Disjunctive Normal Form (DNF)](https://github.com/jonaprieto/agda-prop/blob/master/src/Data/Prop/NormalForms.agda#L202)
  * [Conjunctive Normal Form (CNF)](https://github.com/jonaprieto/agda-prop/blob/master/src/Data/Prop/NormalForms.agda#L270)


### Example


```agda
$ cat test/ex-andreas-abel.agda
open import Data.PropFormula 2 public
...

EM⊃Pierce
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ ((φ ⊃ ψ) ⊃ φ) ⊃ φ

EM⊃Pierce {Γ}{φ}{ψ} =
  ⊃-elim
    (⊃-intro
      (∨-elim {Γ = Γ}
        (⊃-intro
          (weaken ((φ ⊃ ψ) ⊃ φ)
            (assume {Γ = Γ} φ)))
        (⊃-intro
          (⊃-elim
            (assume {Γ = Γ , ¬ φ} ((φ ⊃ ψ) ⊃ φ))
              (⊃-intro
                (⊥-elim
                  ψ
                  (¬-elim
                  (weaken φ
                    (weaken ((φ ⊃ ψ) ⊃ φ)
                      (assume {Γ = Γ} (¬ φ))))
                      (assume {Γ = Γ , ¬ φ , (φ ⊃ ψ) ⊃ φ} φ))))
            ))))
      PEM -- ∀ {Γ} {φ}  → Γ ⊢ φ ∨ ¬ φ

...

```

### References

- Cai, L., Kaposi, A., & Altenkirch, T. (2015)
Formalising the Completeness Theorem of Classical Propositional Logic in Agda.
Retrieved from https://akaposi.github.io/proplogic.pdf
