------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Normal Forms.
------------------------------------------------------------------------------

open import Data.Nat
  using (suc; zero; _+_;_*_)
  renaming (_⊔_ to max; ℕ to Nat )

module Data.PropFormula.NormalForms (n : Nat) where

------------------------------------------------------------------------------

open import Data.Bool.Base
  using ( Bool; true; false; if_then_else_; not)
  renaming (_∧_ to _and_; _∨_ to _or_)

open import Data.Fin  using ( Fin; #_ )
open import Data.List using ( List; [_]; [];  _++_; _∷_ ; concatMap; map )

open import Data.PropFormula.Properties n using ( subst )
open import Data.PropFormula.Syntax n
open import Data.PropFormula.Views  n

open import Relation.Nullary using (yes; no)
open import Data.PropFormula.Theorems n

open import Function using ( _∘_; _$_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; sym )

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Negation Normal Form (NNF)
------------------------------------------------------------------------------

-- Def.
nnf₁ : Nat → PropFormula → PropFormula
nnf₁ (suc n) φ
  with n-view φ
...  | conj φ₁ φ₂   = nnf₁ n φ₁ ∧ nnf₁ n φ₂
...  | disj φ₁ φ₂   = nnf₁ n φ₁ ∨ nnf₁ n φ₂
...  | impl φ₁ φ₂   = nnf₁ n ((¬ φ₁) ∨ φ₂)
...  | biimpl φ₁ φ₂ = nnf₁ n ((φ₁ ⊃ φ₂) ∧ (φ₂ ⊃ φ₁))
...  | nconj φ₁ φ₂  = nnf₁ n ((¬ φ₁) ∨ (¬ φ₂))
...  | ndisj φ₁ φ₂  = nnf₁ n ((¬ φ₁) ∧ (¬ φ₂))
...  | nneg φ₁      = nnf₁ n φ₁
...  | nimpl φ₁ φ₂  = nnf₁ n (¬ (φ₂ ∨ (¬ φ₁)))
...  | nbiim φ₁ φ₂  = nnf₁ n (¬ ((φ₁ ⊃ φ₂) ∧ (φ₂ ⊃ φ₁)))
...  | ntop         = ⊥
...  | nbot         = ⊤
...  | other .φ     = φ
nnf₁ zero φ         = φ

-- Theorem.
nnf₁-lem
  : ∀ {Γ} {φ}
  → (n : Nat)
  → Γ ⊢ φ
  → Γ ⊢ nnf₁ n φ

-- Proof.
nnf₁-lem {Γ} {φ} (suc n) Γ⊢φ
  with n-view φ
...  | conj φ₁ φ₂ =
  ∧-intro
    (nnf₁-lem n (∧-proj₁ Γ⊢φ))
    (nnf₁-lem n (∧-proj₂ Γ⊢φ))
...  | disj φ₁ φ₂ =
  (⊃-elim
    (⊃-intro
     (∨-elim
       (∨-intro₁
         (nnf₁ n φ₂)
         (nnf₁-lem n (assume φ₁)))
       (∨-intro₂
         (nnf₁ n φ₁)
         (nnf₁-lem n (assume φ₂)))))
      Γ⊢φ)
...  | impl φ₁ φ₂   = nnf₁-lem n (⊃-to-¬∨ Γ⊢φ)
...  | biimpl φ₁ φ₂ = nnf₁-lem n (⇔-equiv₁ Γ⊢φ)
...  | nconj φ₁ φ₂  = nnf₁-lem n (¬∧-to-¬∨¬ Γ⊢φ)
...  | ndisj φ₁ φ₂  = nnf₁-lem n (¬∨-to-¬∧¬ Γ⊢φ)
...  | nneg φ₁      = nnf₁-lem n (¬¬-equiv₁ Γ⊢φ)
...  | nimpl φ₁ φ₂  = nnf₁-lem n (subst⊢¬ helper Γ⊢φ)
  where
    helper : Γ ⊢ φ₂ ∨ ¬ φ₁ ⊃ (φ₁ ⊃ φ₂)
    helper = ⊃-intro (¬∨-to-⊃ (∨-comm (assume (φ₂ ∨ ¬ φ₁))))
...  | nbiim φ₁ φ₂  =
  nnf₁-lem n
    (subst⊢¬
      (⊃-intro
        (⇔-equiv₂
          (assume ((φ₁ ⊃ φ₂) ∧ (φ₂ ⊃ φ₁)))))
          Γ⊢φ)
...  | ntop       = ¬-elim Γ⊢φ ⊤-intro
...  | nbot       = ⊤-intro
...  | other .φ   = Γ⊢φ
nnf₁-lem {Γ} {φ} zero Γ⊢φ = Γ⊢φ
--------------------------------------------------------------------------- ∎

-- Complexity measure.
nnf-cm : PropFormula → Nat
nnf-cm φ with n-view φ
... | conj φ₁ φ₂   = nnf-cm φ₁ + nnf-cm φ₂ + 1
... | disj φ₁ φ₂   = nnf-cm φ₁ + nnf-cm φ₂ + 1
... | impl φ₁ φ₂   = 2 * nnf-cm φ₁  + nnf-cm φ₂ + 1
... | biimpl φ₁ φ₂ = 2 * (nnf-cm φ₁ + nnf-cm φ₂) + 3
... | nconj φ₁ φ₂  = nnf-cm (¬ φ₁) + nnf-cm (¬ φ₂) + 1
... | ndisj φ₁ φ₂  = nnf-cm (¬ φ₁) + nnf-cm (¬ φ₂) + 1
... | nneg φ₁      = nnf-cm (¬ φ₁) + 1
... | nimpl φ₁ φ₂  = nnf-cm φ₁ + nnf-cm (¬ φ₂) + 3
... | nbiim φ₁ φ₂  = nnf-cm φ₁ + nnf-cm φ₂ +
                     nnf-cm (¬ φ₁) + nnf-cm (¬ φ₂) + 8
... | ntop         = 1
... | nbot         = 1
... | other .φ     = 1

-- Def.
nnf : PropFormula → PropFormula
nnf φ = nnf₁ (nnf-cm φ) φ

-- Theorem.
nnf-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ nnf φ

-- Proof.
nnf-lem {Γ} {φ} Γ⊢φ = nnf₁-lem (nnf-cm φ) Γ⊢φ
--------------------------------------------------------------------------- ∎

------------------------------------------------------------------------------
-- Disjunctive Normal Form (DNF)
------------------------------------------------------------------------------

-- Def.
dist-∧ : PropFormula → PropFormula
dist-∧ φ with d-view-aux φ
... | case₁ φ₁ φ₂ φ₃ = dist-∧ (φ₁ ∧ φ₃) ∨ dist-∧ (φ₂ ∧ φ₃)
... | case₂ φ₁ φ₂ φ₃ = dist-∧ (φ₁ ∧ φ₂) ∨ dist-∧ (φ₁ ∧ φ₃)
... | other .φ       = φ

-- Theorem.
dist-∧-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ dist-∧ φ

-- Proof.
dist-∧-lem {Γ} {φ} Γ⊢φ with d-view-aux φ
dist-∧-lem {Γ} {.((φ ∨ ψ) ∧ γ)} Γ⊢⟨φ∨ψ⟩∧γ | case₁ φ ψ γ =
  ⊃-elim
    (⊃-intro
      (∨-elim
        (∨-intro₁ (dist-∧ (ψ ∧ γ))
          (dist-∧-lem
            (∧-intro
              (assume φ)
              (weaken φ (∧-proj₂ Γ⊢⟨φ∨ψ⟩∧γ)))))
        (∨-intro₂ (dist-∧ (φ ∧ γ))
          (dist-∧-lem
            (∧-intro
              (assume ψ)
              (weaken ψ (∧-proj₂ Γ⊢⟨φ∨ψ⟩∧γ)))))))
     (∧-proj₁ Γ⊢⟨φ∨ψ⟩∧γ)

dist-∧-lem {Γ} {.(φ ∧ (ψ ∨ γ))} Γ⊢φ∧⟨ψ∨γ⟩ | case₂ φ ψ γ =
  ⊃-elim
    (⊃-intro
      (∨-elim
        (∨-intro₁ (dist-∧ (φ ∧ γ))
          (dist-∧-lem
            (∧-intro
              (weaken ψ (∧-proj₁ Γ⊢φ∧⟨ψ∨γ⟩))
              (assume ψ))))
        (∨-intro₂ (dist-∧ (φ ∧ ψ))
          (dist-∧-lem
            (∧-intro
              (weaken γ (∧-proj₁ Γ⊢φ∧⟨ψ∨γ⟩))
              (assume γ))))))
    (∧-proj₂ Γ⊢φ∧⟨ψ∨γ⟩)
dist-∧-lem {Γ} {.φ} Γ⊢φ             | other φ     = Γ⊢φ
--------------------------------------------------------------------------- ∎

-- Theorem.
from-dist-∧-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ dist-∧ φ
  → Γ ⊢ φ

-- Proof.
from-dist-∧-lem {Γ} {φ} Γ⊢φ with d-view-aux φ
from-dist-∧-lem {Γ} {.((φ ∨ ψ) ∧ γ)} Γ⊢⟨φ∨ψ⟩∧γ | case₁ φ ψ γ =
  ∧-comm
    (∧-dist₂
      (⊃-elim
        (⊃-intro
          (∨-elim
            (∨-intro₁ (γ ∧ ψ)
              (∧-comm
                (from-dist-∧-lem
                  (assume (dist-∧ (φ ∧ γ))))))
            (∨-intro₂ (γ ∧ φ)
              (∧-comm
                (from-dist-∧-lem
                  (assume (dist-∧ (ψ ∧ γ))))))))
        Γ⊢⟨φ∨ψ⟩∧γ))
from-dist-∧-lem {Γ} {.(φ ∧ (ψ ∨ γ))} Γ⊢φ∧⟨ψ∨γ⟩ | case₂ φ ψ γ =
  ∧-dist₂
    (⊃-elim
      (⊃-intro
        (∨-elim
          (∨-intro₁ (φ ∧ γ)
            (from-dist-∧-lem (assume (dist-∧ (φ ∧ ψ)))))
          (∨-intro₂ (φ ∧ ψ)
            (from-dist-∧-lem (assume (dist-∧ (φ ∧ γ)))))))
      Γ⊢φ∧⟨ψ∨γ⟩)
from-dist-∧-lem {Γ} {.φ} Γ⊢φ             | other φ     = Γ⊢φ
--------------------------------------------------------------------------- ∎

-- Def.
dnf-dist : PropFormula → PropFormula
dnf-dist φ with d-view φ
dnf-dist .(φ ∧ ψ) | conj φ ψ = dist-∧ (dnf-dist φ ∧ dnf-dist ψ)
dnf-dist .(φ ∨ ψ) | disj φ ψ = dnf-dist φ ∨ dnf-dist ψ
dnf-dist φ        | other .φ = φ

-- Theorem.
dnf-dist-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ dnf-dist φ

-- Proof.
dnf-dist-lem {Γ} {φ} Γ⊢φ with d-view φ
dnf-dist-lem {Γ} {φ ∧ ψ} Γ⊢φ∧ψ | conj .φ .ψ =
  dist-∧-lem
    (∧-intro
      (dnf-dist-lem (∧-proj₁ Γ⊢φ∧ψ))
      (dnf-dist-lem (∧-proj₂ Γ⊢φ∧ψ)))
dnf-dist-lem {Γ} {φ ∨ ψ} Γ⊢φ∨ψ | disj .φ .ψ =
  ⊃-elim
    (⊃-intro
      (∨-elim
        (∨-intro₁ (dnf-dist ψ) (dnf-dist-lem (assume φ)))
        (∨-intro₂ (dnf-dist φ) (dnf-dist-lem (assume ψ)))))
    Γ⊢φ∨ψ
dnf-dist-lem {Γ} {φ} Γ⊢φ       | other .φ   = Γ⊢φ
--------------------------------------------------------------------------- ∎

-- Theorem.
from-dnf-dist-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ dnf-dist φ
  → Γ ⊢ φ

-- Proof.
from-dnf-dist-lem {_} {φ} Γ⊢φ with d-view φ
from-dnf-dist-lem {_} {φ ∧ ψ} Γ⊢φ∧ψ | conj .φ .ψ =
  ∧-intro
    (from-dnf-dist-lem {φ = φ}
      (∧-proj₁ (from-dist-∧-lem Γ⊢φ∧ψ)))
    (from-dnf-dist-lem {φ = ψ}
      (∧-proj₂ {φ = dnf-dist φ}
        (from-dist-∧-lem Γ⊢φ∧ψ)))
from-dnf-dist-lem {_} {φ ∨ ψ} Γ⊢φ∨ψ | disj .φ .ψ =
  ⊃-elim
    (⊃-intro
      (∨-elim
        (∨-intro₁ ψ
          (from-dnf-dist-lem (assume (dnf-dist φ))))
        (∨-intro₂ φ
          (from-dnf-dist-lem (assume (dnf-dist ψ))))))
    Γ⊢φ∨ψ
from-dnf-dist-lem {_} {φ} Γ⊢φ       | other .φ   = Γ⊢φ
--------------------------------------------------------------------------- ∎


-- Def.
dnf : PropFormula → PropFormula
dnf = dnf-dist ∘ nnf

-- Theorem.
dnf-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ dnf φ

-- Proof.
dnf-lem = dnf-dist-lem ∘ nnf-lem
--------------------------------------------------------------------------- ∎

------------------------------------------------------------------------------
-- Conjunctive Normal Forms (CNF)
------------------------------------------------------------------------------

-- Def.
dist-∨ : PropFormula → PropFormula
dist-∨ φ with c-view-aux φ
dist-∨ .((φ₁ ∧ φ₂) ∨ φ₃) | case₁ φ₁ φ₂ φ₃ =
  dist-∨ (φ₁ ∨ φ₃) ∧ dist-∨ (φ₂ ∨ φ₃)
dist-∨ .(φ₁ ∨ (φ₂ ∧ φ₃)) | case₂ φ₁ φ₂ φ₃ =
  dist-∨ (φ₁ ∨ φ₂) ∧ dist-∨ (φ₁ ∨ φ₃)
dist-∨ φ                 | other .φ       = φ

-- Theorem.
dist-∨-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ dist-∨ φ

-- Proof.
dist-∨-lem {Γ} {φ} Γ⊢φ with c-view-aux φ
dist-∨-lem {Γ} {.((φ ∧ ψ) ∨ γ)} Γ⊢φ | case₁ φ ψ γ =
  ∧-intro
   (dist-∨-lem (∧-proj₁ helper))
   (dist-∨-lem (∧-proj₂ helper))
  where
    helper : Γ ⊢ (φ ∨ γ) ∧ (ψ ∨ γ)
    helper =
      ∧-intro
        (∨-comm (∧-proj₁ (∨-dist₁ (∨-comm Γ⊢φ))))
        (∨-comm (∧-proj₂ (∨-dist₁ (∨-comm Γ⊢φ))))
dist-∨-lem {Γ} {.(φ ∨ (ψ ∧ γ))} Γ⊢φ | case₂ φ ψ γ =
  ∧-intro
    (dist-∨-lem (∧-proj₁ (∨-dist₁ Γ⊢φ)))
    (dist-∨-lem (∧-proj₂ (∨-dist₁ Γ⊢φ)))
dist-∨-lem {Γ} {.φ}  Γ⊢φ | other φ = Γ⊢φ
--------------------------------------------------------------------------- ∎

-- Theorem.
from-dist-∨-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ dist-∨ φ
  → Γ ⊢ φ

-- Proof.
from-dist-∨-lem {Γ} {φ} Γ⊢φ with c-view-aux φ
from-dist-∨-lem {Γ} {.((φ ∧ ψ) ∨ γ)} Γ⊢φ | case₁ φ ψ γ =
  ∨-comm
    (∨-dist₂
      (∧-intro
        (∨-comm
          (from-dist-∨-lem (∧-proj₁ Γ⊢φ)))
        (∨-comm
          (from-dist-∨-lem (∧-proj₂ Γ⊢φ)))))
from-dist-∨-lem {Γ} {.(φ ∨ (ψ ∧ γ))} Γ⊢φ | case₂ φ ψ γ =
  ∨-dist₂
    (∧-intro (from-dist-∨-lem (∧-proj₁ Γ⊢φ))
    (from-dist-∨-lem (∧-proj₂ Γ⊢φ)))
from-dist-∨-lem {Γ} {.φ}  Γ⊢φ | other φ = Γ⊢φ
--------------------------------------------------------------------------- ∎

-- Def.
cnf-dist : PropFormula → PropFormula
cnf-dist φ with d-view φ
cnf-dist .(φ ∧ ψ) | conj φ ψ = cnf-dist φ ∧ cnf-dist ψ
cnf-dist .(φ ∨ ψ) | disj φ ψ = dist-∨ ((cnf-dist φ) ∨ (cnf-dist ψ))
cnf-dist φ        | other .φ = φ

-- Theorem.
cnf-dist-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ cnf-dist φ

-- Proof.
cnf-dist-lem {_} {φ} Γ⊢φ
  with d-view φ
cnf-dist-lem {_} {.(φ ∧ ψ)} Γ⊢φ∧ψ | conj φ ψ =
  ∧-intro (cnf-dist-lem (∧-proj₁ Γ⊢φ∧ψ)) (cnf-dist-lem (∧-proj₂ Γ⊢φ∧ψ))
cnf-dist-lem {_} {.(φ ∨ ψ)} Γ⊢φ∨ψ | disj φ ψ =
  dist-∨-lem
    (⊃-elim
      (⊃-intro
        (∨-elim
          (∨-intro₁ (cnf-dist ψ) (cnf-dist-lem (assume φ)))
          (∨-intro₂ (cnf-dist φ) (cnf-dist-lem (assume ψ)))))
      Γ⊢φ∨ψ)
cnf-dist-lem {_} {.φ} Γ⊢φ | other φ  = Γ⊢φ
--------------------------------------------------------------------------- ∎

-- Theorem.
from-cnf-dist-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ cnf-dist φ
  → Γ ⊢ φ

-- Proof.
from-cnf-dist-lem {_} {φ} Γ⊢cnfdist
  with d-view φ
from-cnf-dist-lem {_} {.(φ ∧ ψ)} Γ⊢cnfdistφ∧ψ | conj φ ψ =
  ∧-intro
    (from-cnf-dist-lem (∧-proj₁ Γ⊢cnfdistφ∧ψ))
    (from-cnf-dist-lem (∧-proj₂ Γ⊢cnfdistφ∧ψ))
from-cnf-dist-lem {_} {.(φ ∨ ψ)} Γ⊢cnfdistφ∨ψ | disj φ ψ =
  ⊃-elim
    (⊃-intro
      (∨-elim
        (∨-intro₁ ψ (from-cnf-dist-lem (assume (cnf-dist φ))))
        (∨-intro₂ φ (from-cnf-dist-lem (assume (cnf-dist ψ))))))
    (from-dist-∨-lem Γ⊢cnfdistφ∨ψ)
from-cnf-dist-lem {_} {.φ} Γ⊢φ | other φ  = Γ⊢φ
--------------------------------------------------------------------------- ∎

-- Def.
cnf : PropFormula → PropFormula
cnf = cnf-dist ∘ nnf

-- Theorem.
cnf-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ cnf φ

-- Proof.
cnf-lem = cnf-dist-lem ∘ nnf-lem  -- ▪

----------------------------------------------------------------------------
-- Testing for a normal form.

is∨ : PropFormula → Bool
is∨ φ
  with d-view φ
is∨ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ = false
is∨ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ = is∨ φ₁ and is∨ φ₂
is∨ φ          | other .φ   = true

is∧∨ : PropFormula → Bool
is∧∨ φ
  with d-view φ
is∧∨ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ = is∧∨ φ₁ and is∧∨ φ₂
is∧∨ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ = is∨ φ₁ and is∨ φ₂
is∧∨ φ          | other .φ   = true

is∧ : PropFormula → Bool
is∧ φ
  with d-view φ
is∧ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ = is∧ φ₁ and is∧ φ₂
is∧ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ = false
is∧ φ          | other .φ   = true

is∨∧ : PropFormula → Bool
is∨∧ φ
  with d-view φ
is∨∧ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ = is∧ φ₁ and is∧ φ₂
is∨∧ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ = is∨∧ φ₁ and is∨∧ φ₂
is∨∧ φ          | other .φ   = true


isNNF : PropFormula → Bool
isNNF φ
  with push-neg-view φ
isNNF φ          | yes .φ     = false
isNNF .(φ₁ ∧ φ₂) | no-∧ φ₁ φ₂ = isNNF φ₁ and isNNF φ₂
isNNF .(φ₁ ∨ φ₂) | no-∨ φ₁ φ₂ = isNNF φ₁ and isNNF φ₂
isNNF φ          | no .φ      = true

isCNF : PropFormula → Bool
isCNF φ = isNNF φ and is∧∨ φ

isDNF : PropFormula → Bool
isDNF φ = isNNF φ and is∨∧ φ
