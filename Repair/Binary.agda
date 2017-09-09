module Binary where

open import Data.Nat
open import Data.Nat.Properties using (+-identityʳ; +-comm)
open import Relation.Binary.PropositionalEquality

data Bin : Set where 
  b0  : Bin       -- 0
  b2  : Bin → Bin -- 2n
  b21 : Bin → Bin -- 2n+1

incr : Bin → Bin
incr b0      = b21 b0
incr (b2 b)  = b21 b
incr (b21 b) = b2 (incr b)

double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

bin→ℕ : Bin → ℕ
bin→ℕ b0      = zero
bin→ℕ (b2 b)  = double (bin→ℕ b) 
bin→ℕ (b21 b) = suc (double (bin→ℕ b))

bin→ℕA : Bin → ℕ
bin→ℕA b0      = zero
bin→ℕA (b2 b)  = 2 * (bin→ℕA b)
bin→ℕA (b21 b) = 1 + 2 * (bin→ℕA b)

bin→ℕB : Bin → ℕ
bin→ℕB b0      = zero
bin→ℕB (b2 b)  = bin→ℕB b + bin→ℕB b
bin→ℕB (b21 b) = suc (bin→ℕB b + bin→ℕB b)

A≡B : (b : Bin) → bin→ℕA b ≡ bin→ℕB b
A≡B b0      = refl
A≡B (b2 b)  rewrite A≡B b | +-identityʳ (bin→ℕB b) = refl
A≡B (b21 b) rewrite A≡B b | +-identityʳ (bin→ℕB b) = refl

doubleSuc : (n : ℕ) → suc (n + suc n) ≡ suc (suc (n + n))
doubleSuc n = cong suc (+-comm n (suc n))

doubleSuc0 : (n : ℕ) → suc (n + suc (n + 0)) ≡ suc (suc (n + (n + 0)))
doubleSuc0 n rewrite +-identityʳ n = doubleSuc n

bin→ℕpreservesIncr : (b : Bin) → bin→ℕ (incr b) ≡ 1 + bin→ℕ b
bin→ℕpreservesIncr b0      = refl
bin→ℕpreservesIncr (b2 b)  = refl
bin→ℕpreservesIncr (b21 b) = cong double (bin→ℕpreservesIncr b)

bin→ℕpreservesIncrA : (b : Bin) → bin→ℕA (incr b) ≡ 1 + bin→ℕA b
bin→ℕpreservesIncrA b0      = refl
bin→ℕpreservesIncrA (b2 b)  = refl
bin→ℕpreservesIncrA (b21 b) rewrite bin→ℕpreservesIncrA b = doubleSuc0 (bin→ℕA b)

bin→ℕpreservesIncrB : (b : Bin) → bin→ℕB (incr b) ≡ 1 + bin→ℕB b
bin→ℕpreservesIncrB b0      = refl
bin→ℕpreservesIncrB (b2 b)  = refl
bin→ℕpreservesIncrB (b21 b) rewrite bin→ℕpreservesIncrB b = doubleSuc (bin→ℕB b)

bin→ℕpreservesIncrA' : (b : Bin) → bin→ℕA (incr b) ≡ 1 + bin→ℕA b
bin→ℕpreservesIncrA' b rewrite A≡B b | A≡B (incr b) = bin→ℕpreservesIncrB b