------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Theorems with different connectives.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.Theorems.Mixies ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Theorems.Implication using ( th244e ; ⇒-equiv )
open import Data.Prop.Theorems.Disjunction using ( ∨-morgan₁ )

open import Data.Prop.Syntax n
open import Function using ( _$_ ; _∘_ )

------------------------------------------------------------------------------


e245b : ∀ {Γ Δ} {φ ψ}
      → Γ ⊢ φ → Δ , φ ⊢ ψ
      → Γ ⨆ Δ ⊢ ψ


-- ⇒-neg : ∀ {Γ} {φ ψ}
--        → Γ ⊢ ¬ (φ ⇒ ψ)
--        → Γ ⊢ φ ∧ ¬ ψ

------------------------------------------------------------------------------
-- Proofs.
------------------------------------------------------------------------------

e245b {Γ}{Δ} seq₁ seq₂ =
  ⇒-elim
    (weaken-Δ₂ Γ $ ⇒-intro seq₂)
    (weaken-Δ₁ Δ seq₁)

-- ⇒-neg {Γ}{φ}{ψ} seq =
--   ∧-intro
--     (⇒-elim (th244e {!pr!}) {!!})
--     (∧-proj₂ pr)
--   where
--     pr : Γ ⊢ ¬ (¬ φ) ∧ ¬ ψ
--     pr = {!!}
