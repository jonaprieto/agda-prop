------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Syntax Experiment definitions.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.SyntaxExperiment ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Bool using (false; true)
open import Data.Prop.Syntax n
open import Data.Prop.Views n
open import Data.Prop.Dec n
open import Data.Prop.Properties n

open import Data.List public

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------------

data _⊢∧_ : Ctxt → List Prop → Set where

  top-intro : ∀ {Γ}
            → Γ ⊢∧ []

  thm-intro : ∀ {Γ} {φ}
            → Γ ⊢ φ
            → Γ ⊢∧ [ φ ]

  ∧-intro   : ∀ {Γ} {φ} {L}
            → Γ ⊢ φ
            → Γ ⊢∧ L
            → Γ ⊢∧ (φ ∷ L)

lemma-++
  : ∀ {Γ} {L₁ L₂}
  → Γ ⊢∧ L₁ → Γ ⊢∧ L₂
  → Γ ⊢∧ (L₁ ++ L₂)
lemma-++ top-intro Γ⊢∧L₁        = Γ⊢∧L₁
lemma-++ (thm-intro x) Γ⊢∧L₁    = ∧-intro x Γ⊢∧L₁
lemma-++ (∧-intro x thm1) Γ⊢∧L₁ = ∧-intro x (lemma-++ thm1 Γ⊢∧L₁)

toList : Prop → List Prop
toList φ with conj-view φ
toList .(φ₁ ∧ φ₂) | conj φ₁ φ₂ = toList φ₁ ++ toList φ₂
toList φ          | other .φ   = [ φ ]

⊢-to-⊢∧
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢∧ toList φ

⊢-to-⊢∧ {_} {φ} Γ⊢φ with conj-view φ
... | conj φ₁ φ₂ = lemma-++ (⊢-to-⊢∧ (∧-proj₁ Γ⊢φ)) (⊢-to-⊢∧ (∧-proj₂ Γ⊢φ))
... | other .φ   = thm-intro Γ⊢φ

∧-proj
  : ∀ {Γ} {φ} {L}
  → Γ ⊢∧ (φ ∷ L)
  → Γ ⊢ φ

∧-proj {_} {_} {.[]} (thm-intro Γ⊢φ)   = Γ⊢φ
∧-proj {_} {_} {L}   (∧-intro Γ⊢φ thm) = Γ⊢φ

toProp : List Prop → Prop
toProp []       = ⊤
toProp (φ ∷ []) = φ
toProp (φ ∷ L)  = φ ∧ (toProp L)

⊢∧-to-⊢
  : ∀ {Γ} {L}
  → Γ ⊢∧ L
  → Γ ⊢ toProp L
⊢∧-to-⊢ {_} {[]}         _                 = ⊤-intro
⊢∧-to-⊢ {_} {x ∷ []}     Γ⊢∧L              = ∧-proj Γ⊢∧L
⊢∧-to-⊢ {_} {x ∷ _ ∷ _} (∧-intro Γ⊢φ Γ⊢∧L) = ∧-intro Γ⊢φ (⊢∧-to-⊢ Γ⊢∧L)

right-assoc-∧ : Prop → Prop
right-assoc-∧  = toProp ∘ toList

thm-right-assoc-∧
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ right-assoc-∧ φ
thm-right-assoc-∧ = ⊢∧-to-⊢ ∘ ⊢-to-⊢∧

find-conjunct : List Prop → Prop → Prop
find-conjunct [] x        = ⊤
find-conjunct (x ∷ xs) y with ⌊ eq x y ⌋
... | false = find-conjunct xs y
... | true  = x

thm-find-conjunct
  : ∀ {Γ} {L}
  → (ψ : Prop)
  → Γ ⊢∧ L
  → Γ ⊢ find-conjunct L ψ

thm-find-conjunct {_} {[]} ψ Γ⊢∧L    = ⊤-intro
thm-find-conjunct {_} {x ∷ L} ψ Γ⊢∧L with ⌊ eq x ψ ⌋
thm-find-conjunct {_} {x ∷ L} ψ Γ⊢∧L   | false with Γ⊢∧L
thm-find-conjunct {_} {x ∷ .[]} ψ Γ⊢∧L | false | thm-intro x₁ = ⊤-intro
thm-find-conjunct {_} {x ∷ L} ψ Γ⊢∧L   | false | ∧-intro x₁ w = thm-find-conjunct ψ w
thm-find-conjunct {_} {x ∷ L} ψ Γ⊢∧L   | true  = ∧-proj Γ⊢∧L

thm-conjunct
  : ∀ {Γ} {φ}
  → (ψ : Prop)
  → Γ ⊢ φ
  → Γ ⊢ find-conjunct (toList φ) ψ
thm-conjunct {_} ψ Γ⊢φ = thm-find-conjunct ψ (⊢-to-⊢∧ Γ⊢φ)

toWeak : (Γ : List Prop) (ψ : Prop) → List Prop
toWeak t f = t , f , f

strip : ∀ {Γ} {φ} → (ψ : Prop) → Γ ⊢ φ → (toWeak Γ ψ) ⊢ φ
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

-- lookup : (xs : List Prop) → Fin (length xs) → Prop
-- lookup [] ()
-- lookup (x ∷ xs) zero    = x
-- lookup (x ∷ xs) (suc n) = lookup xs n

-- record _≈Bag_(xs ys : List Prop) : Set where
--   field
--     bijection : Fin (length xs) ↔ Fin (length ys)
--     related   : ∀ i → lookup xs i ≡ lookup ys (_↔_.to bijection i)

-- data _+_ (A B : Set) : Set where
--   left  : A → A + B
--   right : B → A + B

-- Any : (Prop → Set) → List Prop → Set
-- Any P []       = ⊥₂
-- Any P (x ∷ xs) = P x + Any P xs

-- infix 4 _∈₂_
-- _∈₂_ : Prop → List Prop → Set
-- x ∈₂ xs = Any (λ y → x ≡ y) xs

-- _≈Bag₂_ : List Prop → List Prop → Set
-- xs ≈Bag₂ ys = ∀ x → x ∈₂ xs ↔ x ∈₂ ys
