{-# OPTIONS --without-K #-}

module PatchExamples where

open import Diff

--------------------------------------------------------------------------------

transport : {A : Set} → (P : A → Set) → (x y : A) → x ≡ y → P x → P y
transport P _ _ refl px = px

record Σ (A : Set) (B : A → Set) : Set  where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

--------------------------------------------------------------------------------
-- 1. ≤ variations
-- See Diff.agda for definitions.

-- Derive n≤asn from n≤sn; trivial
{-
n≤sn  : {n : ℕ} → n ≤  suc n
n≤asn : {n : ℕ} → n ≤a suc n
-}

n≤asn' : {n : ℕ} → n ≤a suc n
n≤asn' = ≤→≤a n≤sn

-- Derive ≤atrans from ≤trans; convert arguments and reverse-convert result
{-
≤trans  : {m n p : ℕ} → m ≤  n → n ≤  p → m ≤ p
≤atrans : {m n p : ℕ} → m ≤a n → n ≤a p → m ≤a p
-}

≤atrans' : {m n p : ℕ} → m ≤a n → n ≤a p → m ≤a p
≤atrans' x y = ≤→≤a (≤trans (≤a→≤ x) (≤a→≤ y))

--------------------------------------------------------------------------------
-- 2. + variations

infixl 6 _+ᵣ_

_+ᵣ_ : ℕ → ℕ → ℕ
m +ᵣ zero  = m
m +ᵣ suc n = suc (m +ᵣ n)

n≡0+ᵣn : (n : ℕ) → n ≡ 0 +ᵣ n
n≡0+ᵣn zero    = refl
n≡0+ᵣn (suc n) = cong suc (n≡0+ᵣn n)

+ᵣ-suc' : (m n : ℕ) → suc m +ᵣ n ≡ suc (m +ᵣ n)
+ᵣ-suc' m zero    = refl
+ᵣ-suc' m (suc n) = cong suc (+ᵣ-suc' m n)

+≡+ᵣ : (m n : ℕ) → m + n ≡ m +ᵣ n
+≡+ᵣ zero    n = n≡0+ᵣn n
+≡+ᵣ (suc m) n = trans (cong suc (+≡+ᵣ m n)) (sym (+ᵣ-suc' m n))

---

n≡0+ᵣn' : (n : ℕ) → n ≡ 0 +ᵣ n
--n≡0+ᵣn' n = transport (λ x → n ≡ x) n (0 +ᵣ n) (+≡+ᵣ 0 n) refl 
n≡0+ᵣn' n = +≡+ᵣ 0 n -- simplified

-- note that simplest proof is just refl
n≡n+ᵣ0 : (n : ℕ) → n ≡ n +ᵣ zero
n≡n+ᵣ0 zero    = refl
n≡n+ᵣ0 (suc n) = cong suc (n≡n+ᵣ0 n)

n≡n+ᵣ0' : (n : ℕ) → zero +ᵣ n ≡ n +ᵣ zero
n≡n+ᵣ0' zero    = refl
n≡n+ᵣ0' (suc n) = cong suc (n≡n+ᵣ0' n)

-- This is no longer the theorem we want because it is now trivial.
+ᵣ-suc : (m n : ℕ) → m +ᵣ suc n ≡ suc (m +ᵣ n)
+ᵣ-suc zero    n = refl
+ᵣ-suc (suc m) n = refl  --cong suc (+ᵣ-suc m n)

-- This is the proof we want.  Note that to derive it from +-suc
-- we had to change induction to the other argument along with
-- changing the type.  The proof is then identical.
+ᵣ-suc2 : (m n : ℕ) → suc m +ᵣ n ≡ suc (m +ᵣ n)
+ᵣ-suc2 m zero    = refl
+ᵣ-suc2 m (suc n) = cong suc (+ᵣ-suc2 m n)

-- Must induct on the second argument, and reverse the proof of the first case (using sym)
+ᵣ-comm : (m n : ℕ) → m +ᵣ n ≡ n +ᵣ m
+ᵣ-comm m zero    = sym (n≡n+ᵣ0' m)   -- note that n≡n+ᵣ0, even though it has an identical proof to n≡n+ᵣ0', fails!
+ᵣ-comm m (suc n) = trans (cong suc (+ᵣ-comm m n)) (sym (+ᵣ-suc2 n m))

{-
-- Attempt with rewrite using original rather than updated lemmas.
+-comm' : (m n : ℕ) → m +ᵣ n ≡ n +ᵣ m
+-comm' zero n    = transport (λ x → 0 +ᵣ n ≡ x)
                      (n + 0)
                      (n +ᵣ 0)
                      (+≡+ᵣ n 0)
                      (transport (λ x → x ≡ n + 0)
                         (0 + n)
                         (0 +ᵣ n)
                         (+≡+ᵣ 0 n)
                         (n≡n+0 (n +ᵣ 0))) -- original lemma
+-comm' (suc m) n = {!!} --trans (cong suc (+-comm' m n)) (sym (+-suc n m))
-}

--------------------------------------------------------------------------------
-- 3. Maybe → Decidable

data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥

data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

data Dec (A : Set) : Set where
  yes : A   → Dec A
  no  : ¬ A → Dec A

-- patch
dec→maybe : {A : Set} → Dec A → Maybe A
dec→maybe (yes a) = just a
dec→maybe (no  _) = nothing

--

positiveMaybe : (n : ℕ) → Maybe (Σ ℕ (λ m → suc m ≡ n))
positiveMaybe zero    = nothing
positiveMaybe (suc n) = just (n , refl)

sucn̸n≢0 : (n : ℕ) → ¬ (suc n ≡ 0)
sucn̸n≢0 n ()

positiveDec : (n : ℕ) → Dec (Σ ℕ (λ m → suc m ≡ n))
positiveDec zero    = no  (λ x → sucn̸n≢0 (Σ.proj₁ x) (Σ.proj₂ x))
positiveDec (suc n) = yes (n , refl)

-- trivial patched theorem
positiveMaybe' : (n : ℕ) → Maybe (Σ ℕ (λ m → suc m ≡ n))
positiveMaybe' n = dec→maybe (positiveDec n)

--------------------------------------------------------------------------------
-- 4. Even / Odd

mutual
  data Even : ℕ →  Set where
    ezero : Even zero
    esuc  : {n : ℕ} → Odd n → Even (suc n)

  data Odd  : ℕ → Set where
    oone  : Odd (suc zero)
    osuc  : {n : ℕ} → Even n → Odd (suc n)

data Even' : ℕ →  Set where
  ezero' : Even' zero
  esuc'  : {n : ℕ} → Even' n → Even' (suc (suc n))

data Odd' : ℕ →  Set where
  oone' : Odd' (suc zero)
  osuc' : {n : ℕ} → Odd' n → Odd' (suc (suc n))

-- equivalence

even→even' : {n : ℕ} → Even n → Even' n
even→even' ezero           = ezero'
even→even' (esuc oone)     = esuc' ezero'
even→even' (esuc (osuc n)) = esuc' (even→even' n)

even'→even : {n : ℕ} → Even' n → Even n
even'→even ezero'    = ezero
even'→even (esuc' n) = esuc (osuc (even'→even n))

odd→odd' : {n : ℕ} → Odd n → Odd' n
odd→odd' oone            = oone'
odd→odd' (osuc ezero)    = oone'
odd→odd' (osuc (esuc n)) = osuc' (odd→odd' n)

odd'→odd : {n : ℕ} → Odd' n → Odd n
odd'→odd oone'     = oone
odd'→odd (osuc' n) = osuc (esuc (odd'→odd n))

-- original theorems

even-n+n : (n : ℕ) → Even (n + n)
even-n+n zero = ezero
even-n+n (suc n) = transport Even (suc (suc (n + n))) (suc (n + suc n)) (sym (cong suc (+-suc n n))) (esuc (osuc (even-n+n n))) 

even'-n+n : (n : ℕ) → Even' (n + n)
even'-n+n zero    = ezero'
even'-n+n (suc n) = transport Even' (suc (suc (n + n))) (suc (n + suc n)) (sym (cong suc (+-suc n n))) (esuc' (even'-n+n n)) 

-- patched theorems
-- These are trivial but rely on the old definitions being available.
-- More interesting and much harder is to change the proof to only use the new definitions.

even-n+n' : (n : ℕ) → Even (n + n)
even-n+n' zero    = even'→even ezero'
even-n+n' (suc n) = even'→even (transport Even' (suc (suc (n + n))) (suc (n + suc n)) (sym (cong suc (+-suc n n))) (esuc' (even'-n+n n)))

even'-n+n' : (n : ℕ) → Even' (n + n)
even'-n+n' zero    = even→even' ezero
even'-n+n' (suc n) = even→even' (transport Even (suc (suc (n + n))) (suc (n + suc n)) (sym (cong suc (+-suc n n))) (esuc (osuc (even-n+n n))))

--------------------------------------------------------------------------------
-- 5. Different characterizations of subset types.
-- See http://adam.chlipala.net/cpdt/html/Cpdt.Subset.html
-- To be done.
