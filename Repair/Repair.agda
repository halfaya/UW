module Repair where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

max : ℕ → ℕ → ℕ
max zero n          = n
max (suc m) zero    = suc m
max (suc m) (suc n) = suc (max m n)

data Max : List ℕ → ℕ → Set where
  max[] : Max [] 0
  max∷  : {l : List ℕ} → (n : ℕ) → (m : ℕ) → Max l n → Max l (max m n)

data _∈_ : ℕ → List ℕ → Set where
  here  : {n : ℕ}   → {ns : List ℕ} → n ∈ (n ∷ ns)
  there : {m n : ℕ} → {ns : List ℕ} → n ∈ ns → n ∈ m ∷ ns

data _≤_ : ℕ → ℕ → Set where
  z≤ : {n : ℕ}   → 0 ≤ n
  s≤ : {m n : ℕ} → m ≤ n → suc m ≤ suc n

n+0 : (n : ℕ) → n + 0 ≡ n
n+0 zero    = refl
n+0 (suc n) = cong suc (n+0 n)

m+sucn : (m n : ℕ) → suc (m + n) ≡ m + suc n
m+sucn zero    n = refl
m+sucn (suc m) n = cong suc (m+sucn m n)

+comm : (m n : ℕ) → m + n ≡ n + m
+comm zero    n = sym (n+0 n) 
+comm (suc m) n = trans (cong suc (+comm m n)) (m+sucn n m)

-- NOTE: reversing the first two lines results in grey-out
max2 : (a b c : ℕ) → a ≤ c → a ≤ max b c
max2 _       zero    _       p      = p
max2 zero    (suc b) _       _      = z≤
max2 (suc a) (suc b) (suc c) (s≤ p) = s≤ (max2 a b c p)

max+ : (n a b c : ℕ) → a ≤ n + c → a ≤ n + max b c
max+ _       zero    _ _ _      = z≤
max+ zero    (suc a) b c p      = max2 (suc a) b c p
max+ (suc n) (suc a) b c (s≤ p) = s≤ (max+ n a b c p)

max+comm : (n a b c : ℕ) → a ≤ c + n → a ≤ max b c + n
max+comm n a b c p =
  let x = subst (a ≤_) (+comm c n) p
      y = max+ n a b c x
  in subst (a ≤_) (+comm n (max b c)) y

≤weakening : (m n k : ℕ) → m ≤ n → m ≤ k + n
≤weakening zero    _       _       _      = z≤
≤weakening (suc m) n       zero    p      = p
≤weakening (suc m) zero    (suc k) ()
≤weakening (suc m) (suc n) (suc k) (s≤ p) = subst (suc m ≤_) (m+sucn (suc k) n) (s≤ (≤weakening m n (suc k) p))

≤weakeningc : (m n k : ℕ) → m ≤ n → m ≤ n + k
≤weakeningc m n k p = subst (m ≤_) (+comm k n) (≤weakening m n k p)

infix 4 _≤_
infix 3 _∈_

T1 : (n m : ℕ) → (ns : List ℕ) → n ∈ ns → Max ns m → n ≤ m + 1
T1 _ _            _  () max[]
T1 n .(max m₁ n₁) ns p  (max∷ n₁ m₁ q) = max+comm 1 n m₁ n₁ (T1 n n₁ ns p q)

T1' : (n m : ℕ) → (ns : List ℕ) → n ∈ ns → Max ns m → n ≤ m
T1' _ _            _  () max[]
T1' n .(max m₁ n₁) ns p  (max∷ n₁ m₁ q) = max2 n m₁ n₁ (T1' n n₁ ns p q)

headMaybe : {A : Set} → List A → Maybe A
headMaybe []       = nothing
headMaybe (x ∷ xs) = just x

T2 : (n m : ℕ) → (ns : List ℕ) → headMaybe ns ≡ just n → Max ns m → n ≤ m + 1
T2 n m []        ()   q
T2 n m (.n ∷ ns) refl q = T1 n m (n ∷ ns) here q

T2' : (n m : ℕ) → (ns : List ℕ) → headMaybe ns ≡ just n → Max ns m → n ≤ m + 1
T2' n m []        ()   q

-- T2' n m (.n ∷ ns) refl q = T1' n m (n ∷ ns) here q
-- fails with:
--   m != m + 1 of type ℕ
--   when checking that the expression T1' n m (n ∷ ns) here q has type
--   n ≤ m + 1

-- In this case the error is fairly clear as is the repair--weaken the proof.
T2' n m (.n ∷ ns) refl q = ≤weakeningc n m 1 (T1' n m (n ∷ ns) here q)

-- Alternatively and preferably, strengthen the conclusion.
T2'' : (n m : ℕ) → (ns : List ℕ) → headMaybe ns ≡ just n → Max ns m → n ≤ m
T2'' n m []        ()   q
T2'' n m (.n ∷ ns) refl q = T1' n m (n ∷ ns) here q
