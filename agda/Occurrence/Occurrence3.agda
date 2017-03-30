module Occurrence3 where

open import Data.Empty using (⊥)
open import Function using (_∘_)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

-- comment out exactly one of the following two lines
--open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Sigma using (Σ; _,_; proj₁; proj₂)

-- Lemmas
+0disjoint : Σ ℕ (λ n → + suc n ≡ + zero) → ⊥
+0disjoint (n , ())

+-disjoint : {n : ℕ} → Σ ℕ (λ m → + m ≡ -[1+ n ]) → ⊥
+-disjoint (m , ())

+-disjointS : (n : ℕ) → Σ ℕ (λ m → + suc m ≡ -[1+ n ]) → ⊥
+-disjointS n (m , ())

-- Nat and Pos
isNat : (z : ℤ) → Dec (Σ ℕ (λ n → + n ≡ z))
isNat (+_     n) = yes (n , refl)
isNat (-[1+_] n) = no +-disjoint

Nat : Set
Nat = Σ ℤ (λ z → True (isNat z))

isPos : (z : ℤ) → Dec (Σ ℕ (λ n → + (suc n) ≡ z))
isPos (+    zero)    = no +0disjoint
isPos (+    (suc n)) = yes (n , refl)
isPos (-[1+ n ])     = no (+-disjointS n)

Pos : Set
Pos = Σ ℤ (λ z → True (isPos z))

-- Coercions
pos→nat : Pos → Nat
pos→nat (z , p) = let q = toWitness p in (z , fromWitness (suc (proj₁ q) , proj₂ q))

nat→ℕ : Nat → ℕ
nat→ℕ (+ n      , _) = n
nat→ℕ (-[1+ n ] , ())

-- pred
predℤ : Pos → Nat
predℤ (+ zero     , ())
predℤ (+_ (suc z) , p)  = (+ z , p)
predℤ (-[1+ z ]   , ())

-- f z = if z > 0 then z else 1
f : ℤ → Pos
f z with isPos z
... | yes p = (z , fromWitness p)
... | no  _ = (+ 1 , tt)

-- g z = if z > 0 then z - 1 else 0
g : ℤ → Nat
g z with isPos z
... | yes p = predℤ (z , fromWitness p)
... | no  _ = (+ 0 , tt)
