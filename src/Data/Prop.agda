------------------------------------------------------------------------
-- Agda-Prop Library.
-- Deep Embedding for Propositional Logic.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module Data.Prop (n : ℕ) where

-- Definition of connectives and ⊢ relation.

open import Data.Prop.Syntax n   public

-- Some lemmas and common theorems.

open import Data.Prop.Theorems n public

------------------------------------------------------------------------

open import Data.Bool public using (Bool; true; false; not)
open import Data.Bool public renaming (_∧_ to _&&_; _∨_ to _||_)
open import Data.Fin  public using (Fin; zero; suc; #_)
open import Data.List public using (List; []; _∷_; _++_; [_])
open import Data.Vec  public using (Vec; lookup)

open import Function  public using (_$_)

------------------------------------------------------------------------
