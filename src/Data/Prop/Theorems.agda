------------------------------------------------------------------------------
-- Agda-Prop Library.
-- A compilation of propositional theorems.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.Prop.Theorems ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Theorems.Biimplication n public
open import Data.Prop.Theorems.Classical n     public
open import Data.Prop.Theorems.Conjunction n   public
open import Data.Prop.Theorems.Disjunction n   public
open import Data.Prop.Theorems.Implication n   public
open import Data.Prop.Theorems.Mixies n        public
open import Data.Prop.Theorems.Negation n      public

------------------------------------------------------------------------------
