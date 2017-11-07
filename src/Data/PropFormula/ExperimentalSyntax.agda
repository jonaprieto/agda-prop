------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Syntax Experiment definitions.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.PropFormula.SyntaxExperiment ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Bool using (false; true)

open import Data.PropFormula.Syntax n
open import Data.PropFormula.Views n
open import Data.PropFormula.Dec n
open import Data.PropFormula.Properties n

open import Data.List public

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------------

data _⊢∧_ : Ctxt → List PropFormula → Set where

  empty-intro : ∀ {Γ} → Γ ⊢∧ []

  ∷-intro     : ∀ {Γ} {φ} {L}
              → Γ ⊢ φ
              → Γ ⊢∧ L
              → Γ ⊢∧ (φ ∷ L)

∷-proj₁
  : ∀ {Γ} {φ} {L}
  → Γ ⊢∧ (φ ∷ L)
  → Γ ⊢ φ
∷-proj₁ (∷-intro Γ⊢φ _) = Γ⊢φ

∷-proj₂
  : ∀ {Γ} {φ} {L}
  → Γ ⊢∧ (φ ∷ L)
  → Γ ⊢∧ L
∷-proj₂ (∷-intro _ Γ⊢∧L) = Γ⊢∧L

intro-thm
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢∧ [ φ ]
intro-thm {Γ} {φ} Γ⊢φ = ∷-intro Γ⊢φ empty-intro

++-intro  : ∀ {Γ} {L₁ L₂}
          → Γ ⊢∧ L₁ → Γ ⊢∧ L₂
          → Γ ⊢∧ (L₁ ++ L₂)
++-intro empty-intro th2 = th2
++-intro (∷-intro x th1) th2 = ∷-intro x (++-intro th1 th2)

toList : PropFormula → List PropFormula
toList φ with conj-view φ
toList .(φ₁ ∧ φ₂) | conj φ₁ φ₂ = toList φ₁ ++ toList φ₂
toList φ          | other .φ   = [ φ ]

⊢-to-⊢∧
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢∧ toList φ

⊢-to-⊢∧ {_} {φ} Γ⊢φ with conj-view φ
... | conj φ₁ φ₂ = ++-intro (⊢-to-⊢∧ (∧-proj₁ Γ⊢φ)) (⊢-to-⊢∧ (∧-proj₂ Γ⊢φ))
... | other .φ   = ∷-intro Γ⊢φ empty-intro

toProp : List PropFormula → PropFormula
toProp []       = ⊤
toProp (φ ∷ []) = φ
toProp (φ ∷ L)  = φ ∧ toProp L

⊢∧-to-⊢
  : ∀ {Γ} {L}
  → Γ ⊢∧ L
  → Γ ⊢ toProp L
⊢∧-to-⊢ {_} {[]}         _                 = ⊤-intro
⊢∧-to-⊢ {_} {_ ∷ []}     Γ⊢∧L              = ∷-proj₁ Γ⊢∧L
⊢∧-to-⊢ {_} {x ∷ _ ∷ _} (∷-intro Γ⊢φ Γ⊢∧L) = ∧-intro Γ⊢φ (⊢∧-to-⊢ Γ⊢∧L)

right-assoc-∧ : PropFormula → PropFormula
right-assoc-∧  = toProp ∘ toList

right-assoc-∧-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ right-assoc-∧ φ
right-assoc-∧-lem = ⊢∧-to-⊢ ∘ ⊢-to-⊢∧

find-conjunct : List PropFormula → PropFormula → PropFormula
find-conjunct [] x        = ⊤
find-conjunct (x ∷ xs) y with ⌊ eq x y ⌋
... | false = find-conjunct xs y
... | true  = x

find-conjunct-thm
  : ∀ {Γ} {L}
  → (ψ : PropFormula)
  → Γ ⊢∧ L
  → Γ ⊢ find-conjunct L ψ

find-conjunct-thm {_} {[]} ψ Γ⊢∧L    = ⊤-intro
find-conjunct-thm {_} {x ∷ L} ψ Γ⊢∧L with ⌊ eq x ψ ⌋
find-conjunct-thm {_} {x ∷ L} ψ Γ⊢∧L   | false with Γ⊢∧L
find-conjunct-thm {_} {x ∷ L} ψ Γ⊢∧L   | false | ∷-intro x₁ w = find-conjunct-thm ψ w
find-conjunct-thm {_} {x ∷ L} ψ Γ⊢∧L   | true  = ∷-proj₁ Γ⊢∧L

conjunct-thm
  : ∀ {Γ} {φ}
  → (ψ : PropFormula)
  → Γ ⊢ φ
  → Γ ⊢ find-conjunct (toList φ) ψ
conjunct-thm {_} ψ Γ⊢φ = find-conjunct-thm ψ (⊢-to-⊢∧ Γ⊢φ)

{-
toWeak : (Γ : List PropFormula) (ψ : PropFormula) → List PropFormula
toWeak t f = t , f , f

strip : ∀ {Γ} {φ} → (ψ : PropFormula) → Γ ⊢ φ → (toWeak Γ ψ) ⊢ φ
strip ψ Γ⊢φ = (weaken ψ (weaken ψ Γ⊢φ))

-- Bag Equivalance

-- open import Data.Fin using (Fin; suc; zero; #_)
-- open import Data.List using (length)

-- infixl 3 _↔_
-- record _↔_(A B : Set) : Set where
--   field
--     to      : A → B
--     from    : B → A
--     from-to : ∀ x → from (to x) ≡ x
--     to-from : ∀ x → to (from x) ≡ x

-- lookup : (xs : List PropFormula) → Fin (length xs) → PropFormula
-- lookup [] ()
-- lookup (x ∷ xs) zero    = x
-- lookup (x ∷ xs) (suc n) = lookup xs n

-- record _≈Bag_(xs ys : List PropFormula) : Set where
--   field
--     bijection : Fin (length xs) ↔ Fin (length ys)
--     related   : ∀ i → lookup xs i ≡ lookup ys (_↔_.to bijection i)

-- data _+_ (A B : Set) : Set where
--   left  : A → A + B
--   right : B → A + B

-- Any : (Prop → Set) → List PropFormula → Set
-- Any P []       = ⊥₂
-- Any P (x ∷ xs) = P x + Any P xs

-- infix 4 _∈₂_
-- _∈₂_ : PropFormula → List PropFormula → Set
-- x ∈₂ xs = Any (λ y → x ≡ y) xs

-- _≈Bag₂_ : List PropFormula → List PropFormula → Set
-- xs ≈Bag₂ ys = ∀ x → x ∈₂ xs ↔ x ∈₂ ys
-}
