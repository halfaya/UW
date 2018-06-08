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

data A (n : Nat) : Set where
  mkA : A n

data B : Nat → Set where
  mkB : {n : Nat} → A n → String → B n

x = (_∷ []) "" 

---------

infixr 9 _∘_

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

infixl 1 _≫=_

_≫=_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
_≫=_ = bindTC

map : {A B : Set} → (f : A → B) → List A → List B
map f []       = [] 
map f (x ∷ xs) = f x ∷ map f xs

err : {A : Set} → String → TC A
err = typeError ∘ map strErr ∘ (λ x → "Error:\n" ∷ x ∷ [])

errName : {A : Set} → Name → TC A
errName = typeError ∘ map strErr ∘ (λ x → "ErrorName:\n" ∷ primShowQName x ∷ [])

firstConstructor : Definition → TC Name
firstConstructor (function cs)             = err "bad function"
firstConstructor (data-type pars [])       = err "empty data-type"
firstConstructor (data-type pars (n ∷ _)) = returnTC n
--firstConstructor (data-type pars (_ ∷ n ∷ ns)) = returnTC n
firstConstructor (record-type c _)         = err "bad record-type"
firstConstructor (data-cons d)             = err "bad data-cons"
firstConstructor axiom                     = err "bad axiom"
firstConstructor prim-fun                  = err "bad prim-fun"

getFunction : Definition → TC (List Clause)
getFunction (function cs)       = returnTC cs
getFunction (data-type pars cs) = err "bad data-type"
getFunction (record-type c _)   = err "bad record-type"
getFunction (data-cons d)       = errName d
getFunction axiom               = err "bad axiom"
getFunction prim-fun            = err "bad prim-fun"

macro
  getfun : Name → Term → TC ⊤
  getfun n hole = getDefinition n
    ≫= getFunction
    ≫= (λ cs → inferType (pat-lam cs {-(arg (arg-info visible relevant) (lit (nat zero)) ∷-} []))
    ≫= unify hole
  
  getdef : Name → Term → TC ⊤
  getdef n hole = getDefinition n ≫= firstConstructor ≫= unify hole ∘ lit ∘ name

  getTyp : Name → Term → TC ⊤
  getTyp n hole = getType n ≫= unify hole

  getTyp1 : Name → Term → TC ⊤
  getTyp1 n hole = getDefinition n ≫= firstConstructor ≫= getType ≫= unify hole

s : Name
s = getdef Nat

t : Set₁
t = getTyp Nat

--u : Set
--u = getfun zero
