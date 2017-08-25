module IsoReflect where

open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.String
open import Agda.Builtin.Unit

open import Function using (_∘_)

-- Apply a coercion (from a base type to a new type) to a base type
-- coe : name of coercion from original type to new type
-- base: name of term of the old type converting from
appf : Name → Name → Term
appf coe base = def coe ((arg (arg-info visible relevant) (def base [])) ∷ [])

infixl 1 _≫=_

_≫=_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
_≫=_ = bindTC

map : {A B : Set} → (f : A → B) → List A → List B
map f []       = [] 
map f (x ∷ xs) = f x ∷ map f xs

err : {A : Set} → String → TC A
err = typeError ∘ map strErr ∘ (λ x → "Error:\n" ∷ x ∷ [])

-- orig: name of original type converting from
-- coe : name of coercion from original type to new type
-- base: name of term of the old type converting from
replaceName : Name → Name → Name → Type → Term

replaceName orig coe base   (def f args) with primQNameEquality f orig
replaceName orig coe base   (def f args) | true  = (appf coe base)
replaceName orig coe base t@(def f args) | false = t

replaceName orig coe base t@(var x args)      = t
replaceName orig coe base t@(con c args)      = t
replaceName orig coe base t@(lam v _)         = t
replaceName orig coe base t@(pat-lam cs args) = t

replaceName orig coe base t@(pi _ _)          = t
replaceName orig coe base t@(agda-sort _)     = t
replaceName orig coe base t@(lit _)           = t
replaceName orig coe base t@(meta _ _)        = t
replaceName orig coe base t@unknown           = t

macro
  -- orig: name of original type converting from
  -- coe : name of coercion from original type to new type
  -- base: name of term of the old type converting from
  convert : Name → Name → Name → Term → TC ⊤
  convert orig coe base hole = getType base ≫= (unify hole) ∘ (replaceName orig coe base)
