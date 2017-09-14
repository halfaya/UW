module Binary where

open import Agda.Primitive using (Level)
open import Function using (_∘_)
open import Data.Nat
open import Data.Nat.Properties using (+-identityʳ; +-comm; +-assoc)
open import Relation.Binary.PropositionalEquality

transport : {A : Set} → (P : A → Set) → (x y : A) → x ≡ y → P x → P y
transport P _ _ refl px = px

data Bin : Set where 
  b0  : Bin       -- 0
  b2  : Bin → Bin -- 2n
  b21 : Bin → Bin -- 2n+1

incr : Bin → Bin
incr b0      = b21 b0
incr (b2 b)  = b21 b
incr (b21 b) = b2 (incr b)

----

double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

double+ : (n : ℕ) → double n ≡ n + n
double+ zero    = refl
double+ (suc n) rewrite +-comm n (suc n) = cong (suc ∘ suc) (double+ n)

doubleSuc : (n : ℕ) → suc (n + suc n) ≡ suc (suc (n + n))
doubleSuc n = cong suc (+-comm n (suc n))

doubleSuc0 : (n : ℕ) → suc (n + suc (n + 0)) ≡ suc (suc (n + (n + 0)))
doubleSuc0 n rewrite +-identityʳ n = doubleSuc n

----

2*+ : (n : ℕ) → 2 * n ≡ n + n
2*+ n rewrite +-identityʳ n = refl

----

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

A≡B' : (b : Bin) → bin→ℕA b ≡ bin→ℕB b + 0
A≡B' b0      = refl
A≡B' (b2 b)  rewrite A≡B b | +-assoc (bin→ℕB b) (bin→ℕB b) 0 = refl
A≡B' (b21 b) rewrite A≡B b | +-assoc (bin→ℕB b) (bin→ℕB b) 0 = refl

A→B : (P : ℕ → Set) → (b : Bin) → P (bin→ℕA b) → P (bin→ℕB b + 0)
A→B P b H = transport P (bin→ℕA b) (bin→ℕB b + 0) (A≡B' b) H

A→A : (P : ℕ → Set) → (b : Bin) → P (bin→ℕA b) → P (bin→ℕA b + 0)
A→A P b H = transport P (bin→ℕA b) (bin→ℕA b + 0) (sym (+-identityʳ (bin→ℕA b))) H

bin→ℕC : Bin → ℕ
bin→ℕC b0      = zero
bin→ℕC (b2 b)  = double (bin→ℕC b) 
bin→ℕC (b21 b) = suc (double (bin→ℕC b))

B≡C : (b : Bin) → bin→ℕB b ≡ bin→ℕC b
B≡C b0      = refl
B≡C (b2 b)  rewrite B≡C b = sym (double+ (bin→ℕC b))
B≡C (b21 b) rewrite B≡C b = cong suc (sym (double+ (bin→ℕC b)))

bin→ℕD : Bin → ℕ
bin→ℕD b0      = zero
bin→ℕD (b2 b)  = 2 * (bin→ℕD b)
bin→ℕD (b21 b) = 2 * (bin→ℕD b) + 1

A≡D : (b : Bin) → bin→ℕA b ≡ bin→ℕD b
A≡D b0      = refl
A≡D (b2 b)  rewrite A≡D b = refl
A≡D (b21 b) rewrite A≡D b | +-comm (bin→ℕD b + (bin→ℕD b + 0)) 1 = refl

----

bin→ℕpreservesIncr : (b : Bin) → bin→ℕC (incr b) ≡ 1 + bin→ℕC b
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

bin→ℕpreservesIncrC : (b : Bin) → bin→ℕC (incr b) ≡ 1 + bin→ℕC b
bin→ℕpreservesIncrC b0      = refl
bin→ℕpreservesIncrC (b2 b)  = refl
bin→ℕpreservesIncrC (b21 b) rewrite bin→ℕpreservesIncrC b = refl

bin→ℕpreservesIncrD : (b : Bin) → bin→ℕD (incr b) ≡ 1 + bin→ℕD b
bin→ℕpreservesIncrD b0      = refl
bin→ℕpreservesIncrD (b2 b)  rewrite +-comm (bin→ℕD b + (bin→ℕD b + 0)) 1 = refl
bin→ℕpreservesIncrD (b21 b) rewrite bin→ℕpreservesIncrD b
                                  | +-assoc (bin→ℕD b) (bin→ℕD b + 0) 1
                                  | +-comm (bin→ℕD b + 0) 1 = refl

----

postulate
  extensionality : {a b : Level} → Extensionality a b

A≡Bext : bin→ℕA ≡ bin→ℕB
A≡Bext = extensionality A≡B

bin→ℕpreservesIncrA'' : (b : Bin) → bin→ℕA (incr b) ≡ 1 + bin→ℕA b
bin→ℕpreservesIncrA'' b =
  transport
    (λ f → f (incr b) ≡ 1 + f b)
    bin→ℕB
    bin→ℕA
    (sym A≡Bext)
    (bin→ℕpreservesIncrB b)

----

-- Identical definitions of bin→ℕB and bin→ℕB'

bin→ℕB' : Bin → ℕ
bin→ℕB' b0      = zero
bin→ℕB' (b2 b)  = bin→ℕB' b + bin→ℕB' b
bin→ℕB' (b21 b) = suc (bin→ℕB' b + bin→ℕB' b)

B≡B' : (b : Bin) → bin→ℕB b ≡ bin→ℕB' b
B≡B' b0      = refl
B≡B' (b2 b)  rewrite (B≡B' b) = refl
B≡B' (b21 b) rewrite (B≡B' b) = refl
