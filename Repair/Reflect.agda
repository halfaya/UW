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

data B : Set where

x : Name
x = quote B

y : String
y = primShowQName x

z : Term
z = quoteTerm (λ (x : Bool → Bool) → x true)

e2 : Nat
e2 = quoteGoal e in {!!}

macro
  plus-to-times : Term → Term → TC ⊤
  plus-to-times (def (quote _+_) (a ∷ b ∷ [])) hole = unify hole (def (quote _*_) (a ∷ b ∷ []))
  plus-to-times v hole = unify hole v

thm : (a b : Nat) → plus-to-times (a + b) ≡ a * b
thm a b = refl
