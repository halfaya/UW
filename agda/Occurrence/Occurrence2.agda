module Occurrence2 where

open import Data.Unit using (⊤; tt)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- comment out exactly one of the following two lines
--open import Data.Product using (Σ; _,_)
open import Sigma using (Σ; _,_)

isNat : ℤ → Bool
isNat (+ _)      = true
isNat (-[1+ _ ]) = false

isPos : ℤ → Bool
isPos (+ (suc _)) = true
isPos _           = false

Nat : Set
Nat = Σ ℤ (λ z -> isNat z ≡ true)

Pos : Set
Pos = Σ ℤ (λ z -> isPos z ≡ true)

isNat2 : (z : ℤ) → Σ Bool (λ b → if b then isNat z ≡ true else ⊤)
isNat2 z with isNat z
... | true  = (true , refl)
... | false = (false , tt)

isPos2 : (z : ℤ) → Σ Bool (λ b → if b then isPos z ≡ true else ⊤)
isPos2 z with isPos z
... | true  = (true , refl)
... | false = (false , tt)

pos→nat : Pos → Nat
pos→nat (+ zero    , ())
pos→nat (+ (suc n) , p) = + (suc n) , refl
pos→nat (-[1+ _ ]  , ())

nat→ℕ : Nat → ℕ
nat→ℕ (+ n      , _) = n
nat→ℕ (-[1+ n ] , ())

predℤ : Pos → Nat
predℤ (+ zero    , ())
predℤ (+ (suc n) , p) = + n , refl
predℤ (-[1+ _ ]  , ())

f : ℤ → Pos
f z with isPos2 z
... | (true  , p) = (z , p)
... | (false , p) = (+ 1 , refl)

g : ℤ → Nat
g z with isPos2 z
... | (true  , p) = predℤ (z , p)
... | (false , p) = (+ 0 , refl)
