module Sat where

open import Data.Bool using (Bool; true; false)
open import Data.Nat  using (ℕ)

data Atom : Set where
  ⊤   : Atom
  ⊥   : Atom
  var : ℕ → Atom

data Literal : Set where
  atom : Atom → Literal
  ¬_   : Atom → Literal

data Prop : Set where
  lit : Literal → Prop
  _∨_ : Prop → Prop → Prop
  _∧_ : Prop → Prop → Prop
  ¬_  : Prop → Prop

_⟶_ : Prop → Prop → Prop
a ⟶ b = (¬ a) ∨ b

_⟷_ : Prop → Prop → Prop
a ⟷ b = (a ∧ b) ∨ ((¬ a) ∧ (¬ b))

-- Normal forms

data NProp : Set where
  lit : Literal → NProp
  _∨_ : NProp → NProp → NProp
  _∧_ : NProp → NProp → NProp

NNF : Prop → NProp
NNF (lit a)          = lit a
NNF (a ∨ b)          = NNF a ∨ NNF b
NNF (a ∧ b)          = NNF a ∧ NNF b
NNF (¬ lit (atom a)) = lit (¬ a)
NNF (¬ lit (¬ a))    = lit (atom a)
NNF (¬ (a ∨ b))      = NNF (¬ a) ∧ NNF (¬ b)
NNF (¬ (a ∧ b))      = NNF (¬ a) ∨ NNF (¬ b)
NNF (¬ (¬ a))        = NNF a

data DClause : Set where
  lit : Literal → DClause
  _∧_ : Literal → DClause → DClause

data DProp : Set where
  clause : DClause → DProp
  _∨_    : DClause → DProp → DProp

_++_ : DProp → DProp → DProp
clause a ++ c = a ∨ c
(a ∨ b)  ++ c = a ∨ (b ++ c)

DNF : NProp → DProp
DNF (lit a) = clause (lit a)
DNF (a ∨ b) = DNF a ++ DNF b
DNF (lit a ∧ b) with DNF b
DNF (lit a ∧ b) | clause c = clause (a ∧ c)
DNF (lit a ∧ b) | c ∨ d    = (a ∧ c) ∨ d
DNF ((a ∨ b) ∧ c) = DNF (a ∧ c) ++ DNF (b ∧ c)
DNF ((a ∧ b) ∧ c) = {!!}

-- (A ∧ (B ∧ (C ∨ E))) ∧ D
-- (A ∧ ((B ∧ C) ∨ (B ∧ E))) ∧ D

data CClause : Set where
  lit : Literal → CClause
  _∨_ : Literal → CClause → CClause

data CProp : Set where
  clause : CClause → CProp
  _∧_    : CClause → CProp → CProp

simplifyc : CClause → CClause
simplifyc c@(lit (atom _))       = c
simplifyc (lit (¬ ⊤))            = lit (atom ⊥)
simplifyc (lit (¬ ⊥))            = lit (atom ⊤)
simplifyc c@(lit (¬ var _))      = c
simplifyc (atom ⊤ ∨ c)           = lit (atom ⊤)
simplifyc (atom ⊥ ∨ c)           = simplifyc c
simplifyc (a@(atom (var _)) ∨ c) = a ∨ simplifyc c
simplifyc ((¬ ⊤) ∨ c)            = simplifyc c
simplifyc ((¬ ⊥) ∨ c)            = lit (atom ⊤)
simplifyc (a@(¬ var _) ∨ c)      = a ∨ simplifyc c

-- Assumes arguments are simplified and clause is not ⊤ or ⊥
-- Assumes clause and prop are ∧ed
simplify2 : CClause → CProp → CProp
simplify2 c (clause (lit (atom ⊤)))         = clause c
simplify2 c p@(clause (lit (atom ⊥)))       = p
simplify2 c p@(clause (lit (atom (var _)))) = c ∧ p
simplify2 c p@(clause (lit (¬ _)))          = c ∧ p
simplify2 c p@(clause (_ ∨ _))              = c ∧ p
simplify2 c p@(_ ∧ _)                       = c ∧ p

simplify : CProp → CProp
simplify (clause c) = clause (simplifyc c)
simplify (c ∧ p) with simplifyc c
simplify (c ∧ p) | lit (atom ⊤)       = simplify p
simplify (c ∧ p) | lit (atom ⊥)       = clause (lit (atom ⊥))
simplify (c ∧ p) | lit (atom (var x)) = simplify2 (lit (atom (var x))) (simplify p)
simplify (c ∧ p) | lit (¬ x)          = simplify2 (lit (¬ x)) (simplify p)
simplify (c ∧ p) | a ∨ b              = simplify2 (a ∨ b) (simplify p)
