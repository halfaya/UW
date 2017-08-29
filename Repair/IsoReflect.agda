module IsoReflect where

open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection
open import Agda.Builtin.String
open import Agda.Builtin.Unit

open import Function using (_∘_)

not : Bool → Bool
not false = true
not true  = false

infixl 1 _≫=_

_≫=_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
_≫=_ = bindTC

map : {A B : Set} → (f : A → B) → List A → List B
map f []       = [] 
map f (x ∷ xs) = f x ∷ map f xs

err : {A : Set} → String → TC A
err = typeError ∘ map strErr ∘ (λ x → "Error:\n" ∷ x ∷ [])

terr : {A : Set} → Term → TC A
terr = typeError ∘ map termErr ∘ (λ x → x ∷ [])

-- Create a list [n-1, n-2, ... 0]
countdownList : Nat → List Nat
countdownList zero    = []
countdownList (suc n) = n ∷ countdownList n

-- Apply a reverse coercion (from a new type to a base type) to a deBruijn index
-- coer : name of reverse coercion from new type to original type
-- n:   : deBruijn index
appRevCoe : Name → Nat → Arg Term
appRevCoe coer n = arg (arg-info visible relevant) (def coer ((arg (arg-info visible relevant) (var n [])) ∷ []))

-- Apply a coercion (from a base type to a new type) to a base type
-- coe : name of coercion from original type to new type
-- coer : name of reverse coercion from new type to original type
-- base: name of term of the old type converting from
appCoe : Name → Name → Name → Nat → Term
appCoe coe coer base n =
  def coe (arg (arg-info visible relevant) (def base (map (appRevCoe coer) (countdownList n))) ∷ [])

-- orig : name of original type converting from
-- coe  : name of coercion from original type to new type
-- coer : name of reverse coercion from new type to original type
-- base : name of term of the old type converting from
-- cov  : true if covariant; false if contravariant
-- n    : last index of a variable for a pi type (TODO: generalize)
replaceName : Name → Name → Name → Name → Bool → Nat → Type → Term

replaceName orig coe coer base cov n   (def f args) with primQNameEquality f orig
replaceName orig coe coer base cov n   (def f args) | true  = (appCoe coe coer base n)
replaceName orig coe coer base cov n t@(def f args) | false = t

replaceName orig coe coer base cov n t@(var x args)      = t
replaceName orig coe coer base cov n t@(con c args)      = t
replaceName orig coe coer base cov n t@(lam v _)         = t
replaceName orig coe coer base cov n t@(pat-lam cs args) = t

replaceName orig coe coer base cov n t@(agda-sort _)     = t
replaceName orig coe coer base cov n t@(lit _)           = t
replaceName orig coe coer base cov n t@(meta _ _)        = t
replaceName orig coe coer base cov n t@unknown           = t

-- currently assumes all pi arguments are of the original type
replaceName orig coe coer base cov n (pi (arg (arg-info visible   _) _) (abs s t)) =
  lam visible (abs s (replaceName orig coe coer base cov (suc n) t))
replaceName orig coe coer base cov n (pi (arg (arg-info hidden    _) _) (abs s t)) =
  replaceName orig coe coer base cov n t
replaceName orig coe coer base cov n (pi (arg (arg-info instance′ _) _) (abs s t)) =
  replaceName orig coe coer base cov n t

macro
  -- orig : name of original type converting from
  -- coe  : name of coercion from original type to new type
  -- coer : name of reverse coercion from new type to original type
  -- base : name of term of the old type converting from
  convert : Name → Name → Name → Name → Term → TC ⊤
  convert orig coe coer base hole = getType base ≫= normalise ≫= (unify hole) ∘ (replaceName orig coe coer base true 0)

  printType : Name → Term → TC ⊤
  printType n hole = getType n ≫= terr
