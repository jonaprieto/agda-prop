------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Deep Embedding for Propositional Logic.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module Data.PropFormula ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Dec n         public
open import Data.PropFormula.NormalForms n public
open import Data.PropFormula.Properties n  public
open import Data.PropFormula.Syntax n      public
open import Data.PropFormula.Theorems n    public

open import Data.Bool public
  using    ( Bool; true; false; not )
  renaming ( _∧_ to _&&_; _∨_ to _||_ )

open import Data.Fin  public using ( Fin; zero; suc; #_ )
open import Data.List public using ( List; []; _∷_; _++_; [_] )
open import Data.Vec  public using ( Vec; lookup )

open import Function  public using ( _$_ )

------------------------------------------------------------------------------
