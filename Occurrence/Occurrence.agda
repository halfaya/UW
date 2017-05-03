module Occurrence where

open import Data.Product
open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality

data ⊤ : Set where
  tt : ⊤

data ℤ : Set where
  nonneg : ℕ → ℤ
  negsuc : ℕ → ℤ

isNat : ℤ → Bool
isNat (nonneg x) = true
isNat (negsuc x) = false

isPos : ℤ → Bool
isPos (nonneg (suc x)) = true
isPos _                = false

x = isPos (nonneg 2)

int : Set
int = Σ[ z ∈ ℤ ] ⊤

nat : Set
nat = Σ[ z ∈ ℤ ] isNat z ≡ true

pos : Set
pos = Σ[ z ∈ ℤ ] isPos z ≡ true

isNat2 : (z : int) → Σ[ b ∈ Bool ] (if b then isNat (proj₁ z) ≡ true else ⊤)
isNat2 (z , _) with isNat z
... | true  = (true , refl)
... | false = (false , tt)

isPos2 : (z : int) → Σ[ b ∈ Bool ] (if b then isPos (proj₁ z) ≡ true else ⊤)
isPos2 (z , _) with isPos z
... | true  = (true , refl)
... | false = (false , tt)

xpred : pos → nat
xpred (nonneg zero , ())
xpred (nonneg (suc x) , p) = nonneg x , refl
xpred (negsuc x , ())

f : int → pos
f z with isPos2 z
... | (true  , p) = (proj₁ z , p)
... | (false , p) = (nonneg 1 , refl)

g : int → nat
g z with isPos2 z
... | (true  , p) = xpred (proj₁ z , p)
... | (false , p) = (nonneg 0 , refl)  
