# Agda-Prop [![Build Status](https://travis-ci.org/jonaprieto/agda-prop.svg?branch=master)](https://travis-ci.org/jonaprieto/agda-prop) [![DOI](https://zenodo.org/badge/84277944.svg)](https://zenodo.org/badge/latestdoi/84277944)

This is an library to work with propositional logic based on a deep embedding.
It contains a compilation of some useful theorems and properties to work with.

<!-- TOC depthFrom:2 depthTo:6 withLinks:1 updateOnSave:1 orderedList:0 -->

- [Quick Start](#quick-start)
	- [Requirements](#requirements)
	- [Installation](#installation)
- [Usage](#usage)
	- [Theorems](#theorems)
	- [Examples](#examples)
	- [References](#references)
	- [Contributions](#contributions)

<!-- /TOC -->

## Quick Start

This library provides us two data types: `Prop` and `_⊢_`.
We define the following constructors for Prop data type.

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
And for the turnstile, we have a list of inference rules:

```agda
data _⊢_ : (Γ : Ctxt)(φ : Prop) → Type where

-- Hyp.

  assume   : ∀ {Γ} → (φ : Prop)           → Γ , φ ⊢ φ

  axiom    : ∀ {Γ} → (φ : Prop)           → φ ∈ Γ
                                          → Γ ⊢ φ

  weaken   : ∀ {Γ} {φ} → (ψ : Prop)       → Γ ⊢ φ
                                          → Γ , ψ ⊢ φ
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

See examples more below.


### Requirements

* [Agda](https://github.com/agda/agda) version 2.5.1+
* [Agda Standard Library](https://github.com/agda/agda-stdlib/) compatible with your Agda version

### Installation

Clone this repository:

```
$ git clone http://github.com/jonaprieto/agda-prop.git
```

Add the path of this library to your library manager file, located in `~/.agda/libraries`. For instance, a valid file looks similar to this one:

```bash
$ cat $HOME/.agda/libraries
/home/jonaprieto/agda-stdlib/standard-library.agda-lib
/home/jonaprieto/agda-prop/agda-prop.agda-lib
```

If you  need more instructions to install libraries for Agda, [Here](http://agda.readthedocs.io/en/latest/tools/package-system.html#installing-libraries)
is a good link to start.

## Usage
### Theorems

The theorems have a name based on their main connective, their purpose or their source.
We added sub-indices for those theorems that differ a little with other one.

* [List of Theorems][theorems]
  * [Conjunction][CONJ]
  * [Implication][IMPL]
  * [Disjunction][DISJ]
  * [Negation][NEG]
  * [Biimplication][BICON]

[theorems]: https://github.com/jonaprieto/agda-prop/tree/master/src/Data/Prop/Theorems
[CONJ]:https://raw.githubusercontent.com/jonaprieto/agda-prop/master/src/Data/Prop/Theorems/Conjunction.agda
[IMPL]:https://raw.githubusercontent.com/jonaprieto/agda-prop/master/src/Data/Prop/Theorems/Implication.agda
[DISJ]:https://raw.githubusercontent.com/jonaprieto/agda-prop/master/src/Data/Prop/Theorems/Disjunction.agda
[NEG]:https://raw.githubusercontent.com/jonaprieto/agda-prop/master/src/Data/Prop/Theorems/Negation.agda
[BICON]:https://raw.githubusercontent.com/jonaprieto/agda-prop/master/src/Data/Prop/Theorems/Biimplication.agda


### Examples

As example, we type-checked natural deduction proofs of some exercises from
[Type Theory CM0859](http://www1.eafit.edu.co/asr/courses/type-theory-CM0859/exercises.pdf)
course:

```agda
-- $ cat test/ex-andreas-abel.agda
open import Data.Prop 2 public

ex3
  : ∀ {φ ψ ω}
  → ∅ ⊢ (φ ∧ (ψ ∨ ω)) ⇒ ((φ ∧ ψ) ∨ (φ ∧ ω))

ex3 {φ}{ψ}{ω} =
  ⇒-intro
  (⇒-elim
    (⇒-intro
      (∨-elim {Γ = ∅ , (φ ∧ (ψ ∨ ω))}
        (∨-intro₁
          (φ ∧ ω)
          (∧-intro
            (∧-proj₁ (weaken ψ (assume {Γ = ∅} (φ ∧ (ψ ∨ ω)))))
            (assume {Γ = ∅ , (φ ∧ (ψ ∨ ω)) } ψ)))
        (∨-intro₂
          (φ ∧ ψ)
          (∧-intro
            (∧-proj₁ (weaken ω (assume {Γ = ∅} (φ ∧ (ψ ∨ ω)))))
            (assume {Γ = ∅ , (φ ∧ (ψ ∨ ω))} ω )))))
    (∧-proj₂ (assume {Γ = ∅} (φ ∧ (ψ ∨ ω)))))

```

### References

- Jonathan Prieto-Cubides and Alejandro Gomez-Londoño.
  [*A proof tool for translating TSTP proofs to Agda code*](https://github.com/jonaprieto/tstp2agda/tree/deep)

- Leran Cai, Ambrus Kaposi, and Thorsten Altenkirch. *Formalising the Completeness
  Theorem of Classical Propositional Logic in Agda (Proof Pearl)*. The formalisation
  is available at http://bitbucket.org/Leran/.

### Contributions

`Data.Prop.Theorems` modules contain some postulates waiting to be proved. Go ahead!
