# agda-prop
A library to work with propositional logic based on a deep embedding.

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
  ¬_   : (φ : Prop) → Prop       -- Negation.
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
* [Agda Standard Library](https://github.com/agda/agda-stdlib/)

### Installation

Clone this repository:

```
$ git clone http://github.com/jonaprieto/agda-prop.git
```

Add the path of this library to your library manager file, usually
located in `~/.agda/libraries`. For instance, my file looks like:

```bash
$ cat $HOME/.agda/libraries
/home/jonaprieto/agda-stdlib/standard-library.agda-lib
/home/jonaprieto/agda-prop/agda-prop.agda-lib.agda
```

[Here](http://agda.readthedocs.io/en/latest/tools/package-system.html#installing-libraries)
we can find more information about installing libraries in Agda.

### Usage Examples

We type-checked natural deductions proofs of the exercises in the
[Type Theory CM0859](http://www1.eafit.edu.co/asr/courses/type-theory-CM0859/exercises.pdf)
course.

Then, for instance without any assumptions, we can prove:

```agda
-- $ cat test/ex-andreas-abel.agda

open import Data.Prop 2 public

ex1 : ∀ {φ} → ∅ ⊢ φ ⇒ φ
ex1 {φ} = ⇒-intro (assume {Γ = ∅} φ)

ex2 : ∀ {φ ψ} → ∅ ⊢ (φ ∧ (φ ⇒ ψ)) ⇒ ψ
ex2 {φ} {ψ} =
  ⇒-intro
    (⇒-elim
      (∧-proj₂ (assume {Γ = ∅} (φ ∧ (φ ⇒ ψ))))
      (∧-proj₁ (assume {Γ = ∅}  (φ ∧ (φ ⇒ ψ)))))

ex3 : ∀ {φ ψ ω} → ∅ ⊢ (φ ∧ (ψ ∨ ω)) ⇒ ((φ ∧ ψ) ∨ (φ ∧ ω))
ex3 {φ} {ψ} {ω} =
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

### Contributions

There are postulates in `Data.Prop.Theorems` files that need a proof, and
other missing ones lemmas and theorems. Proofs are welcomed.
