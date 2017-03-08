# agda-prop
A library to work with propositional logic based on a deep embedding.

## Quick Start

This library provides us two data types: `Prop` and `⊢`.
The Prop data type define the following constructors.

```agda
data Prop : Type where
  Var              : Fin n → Prop
  ⊤ ⊥              : Prop
  _∧_ _∨_ _⇒_ _⇔_ : (φ ψ : Prop) → Prop
  ¬_               : (φ : Prop) → Prop
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

More information about managing libraries in Agda
[here](http://agda.readthedocs.io/en/latest/tools/package-system.html#installing-libraries)

### Usage Examples

We type-checked natural deductions proofs of the exercises in the
[Type Theory CM0859](http://www1.eafit.edu.co/asr/courses/type-theory-CM0859/exercises.pdf)
course.

Then, for instance without any assumptions, we can prove:

```agda
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
  (⇒-elim {Γ = ∅ , (φ ∧ (ψ ∨ ω))}
    (⇒-intro {Γ = ∅ , (φ ∧ (ψ ∨ ω))}
      (∨-elim {Γ = ∅ , (φ ∧ (ψ ∨ ω))}
        (∨-intro₁ {Γ = ∅ , (φ ∧ (ψ ∨ ω)) , ψ}
          (φ ∧ ω)
          (∧-intro
            (∧-proj₁ (weaken ψ (assume {Γ = ∅} (φ ∧ (ψ ∨ ω)))))
            (assume {Γ = ∅ , (φ ∧ (ψ ∨ ω)) } ψ)))
        (∨-intro₂ {Γ = ∅ , (φ ∧ (ψ ∨ ω)) , ω}
          (φ ∧ ψ)
          (∧-intro
            (∧-proj₁ (weaken ω (assume {Γ = ∅} (φ ∧ (ψ ∨ ω)))))
            (assume {Γ = ∅ , (φ ∧ (ψ ∨ ω))} ω )))))
    (∧-proj₂ (assume {Γ = ∅} (φ ∧ (ψ ∨ ω)))))

ex4 : ∀ {φ ψ} → ∅ ⊢ (¬ φ ∨ ψ) ⇒ (φ ⇒ ψ)
ex4 {φ} {ψ} =
  ⇒-intro $
    ∨-elim {Γ = ∅}
      (⇒-intro
        (⊥-elim ψ
          (¬-elim
            (weaken φ (assume {Γ = ∅} (¬ φ)))
            (assume {Γ = ∅ , ¬ φ} φ))))
      (⇒-intro (weaken φ (assume {Γ = ∅} ψ)))

```

### Contributions

There are postulates in `Data.Prop.Theorems` files that need a proof, and
other missing ones lemmas and theorems. That's is the challenge.
