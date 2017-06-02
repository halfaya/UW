module Reflect where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Agda.Builtin.Float
open import Agda.Builtin.Int
open import Agda.Builtin.Equality

data A : Set where
  mkA : A

data B : Set where
  mkB : B

x = (_∷ []) "" 

---------

infixr 9 _∘_

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

infixl 1 _≫=_

_≫=_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
_≫=_ = bindTC

err : {A : Set} → String → TC A
err = typeError ∘ (_∷ []) ∘ strErr

firstConstructor : Definition → TC Name
firstConstructor (function cs)             = err "bad function"
firstConstructor (data-type pars [])       = err "empty data-type"
firstConstructor (data-type pars (n ∷ ns)) = returnTC n
firstConstructor (record-type c)           = err "bad record-type"
firstConstructor (data-cons d)             = err "bad data-cons"
firstConstructor axiom                     = err "bad axiom"
firstConstructor prim-fun                  = err "bad prim-fun"

macro
  getdef : Name → Term → TC ⊤
  getdef n hole = getDefinition n ≫= firstConstructor ≫= unify hole ∘ lit ∘ name

s : Name
s = getdef A
