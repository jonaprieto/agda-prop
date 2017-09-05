------------------------------------------------------------------------------
-- Agda-Prop Library.
-- A compilation of propositional theorems.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.PropFormula.Theorems ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Theorems.Biimplication n public
open import Data.PropFormula.Theorems.Classical n     public
open import Data.PropFormula.Theorems.Conjunction n   public
open import Data.PropFormula.Theorems.Disjunction n   public
open import Data.PropFormula.Theorems.Implication n   public
open import Data.PropFormula.Theorems.Mixies n        public
open import Data.PropFormula.Theorems.Negation n      public
open import Data.PropFormula.Theorems.Weakening n     public

------------------------------------------------------------------------------
