{-# OPTIONS --without-K --safe #-}

module Natty where

open import Data.Nat using (ℕ; zero; suc)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

data Bin : Set where
  b0 : Bin         -- 0
  s1 : Bin → Bin   -- 2b+1
  s2 : Bin → Bin   -- 2b+2 (= 2(b+1))

bsuc : Bin → Bin
bsuc b0     = s1 b0
bsuc (s1 b) = s2 b
bsuc (s2 b) = s1 (bsuc b)

data Natty : Bin → Set where
  n0   : Natty b0
  nsuc : (b : Bin) → Natty b → Natty (bsuc b)

s1Natty : (b : Bin) → Natty b → Natty (s1 b)
s1Natty .b0       n0         = nsuc b0 n0
s1Natty .(bsuc b) (nsuc b n) = nsuc (s2 b) (nsuc (s1 b) (s1Natty b n))

natty : (b : Bin) → Natty b
natty b0     = n0
natty (s1 b) =              s1Natty b (natty b)
natty (s2 b) = nsuc (s1 b) (s1Natty b (natty b))

natPeano : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
natPeano P p0 psuc zero    = p0
natPeano P p0 psuc (suc n) = psuc n (natPeano P p0 psuc n)

natPeanoId : ℕ → ℕ
natPeanoId = natPeano (λ _ → ℕ) zero (λ _ n → suc n)

natPeanoIdSuc : (n : ℕ) → natPeanoId (suc n) ≡ suc (natPeanoId n)
natPeanoIdSuc n = refl

natPeanoIdId : (n : ℕ) → natPeanoId n ≡ n
natPeanoIdId = natPeano (λ n → natPeanoId n ≡ n) refl (λ n ih → trans (natPeanoIdSuc n) (cong suc ih))

-- Since (natPeanoIdSuc' n) is just refl, the proof collapses as follows.
natPeanoIdId' : (n : ℕ) → natPeanoId n ≡ n
natPeanoIdId' = natPeano (λ n → natPeanoId n ≡ n) refl (λ n ih → cong suc ih)

----------
-- Alternative direct proof using subst
natPeanoIdId'' : (n : ℕ) → natPeanoId n ≡ n
natPeanoIdId'' = natPeano (λ n → natPeanoId n ≡ n) refl (λ n ih → subst (λ x → suc x ≡ suc n) (sym ih) refl)

-- Even though this proof is just refl (see natPeanoIdSuc) we can also prove it using natPeanoIdId'' and 2 rewrites
natPeanoIdSuc' : (n : ℕ) → natPeanoId (suc n) ≡ suc (natPeanoId n)
natPeanoIdSuc' n rewrite natPeanoIdId'' n = refl
--------

nattyPeano : (P : Bin → Set) → P b0 → ((b : Bin) → P b → P (bsuc b)) → (b : Bin) → Natty b → P b
nattyPeano P p0 psuc .b0       n0         = p0
nattyPeano P p0 psuc .(bsuc b) (nsuc b n) = psuc b (nattyPeano P p0 psuc b n)

binPeano : (P : Bin → Set) → P b0 → ((b : Bin) → P b → P (bsuc b)) → (b : Bin) → P b
binPeano P p0 psuc b = nattyPeano P p0 psuc b (natty b)

binPeanoId : Bin → Bin
binPeanoId = binPeano (λ _ → Bin) b0 (λ _ b → bsuc b)

-- original version
binNattySuc' : (b : Bin) → Natty b → natty (bsuc b) ≡ nsuc b (natty b)
binNattySuc' .b0            n0                                               = refl
binNattySuc' .(bsuc b0)     (nsuc b0 n)                                      = refl
binNattySuc' .(bsuc (s1 b)) (nsuc (s1 b) n) rewrite binNattySuc' b (natty b) = refl
binNattySuc' .(bsuc (s2 b)) (nsuc (s2 b) n)                                  = refl

-- simplified version
binNattySuc : (b : Bin) → natty (bsuc b) ≡ nsuc b (natty b)
binNattySuc b0     = refl
binNattySuc (s1 b) rewrite binNattySuc b = refl
binNattySuc (s2 b) rewrite binNattySuc b = refl

binPeanoSuc : (P : Bin → Set) → (p0 : P b0) → (psuc : (b : Bin) → P b → P (bsuc b)) → (b : Bin) →
  binPeano P p0 psuc (bsuc b) ≡ psuc b (binPeano P p0 psuc b)
binPeanoSuc P p0 psuc b rewrite binNattySuc b = refl  

binPeanoIdSuc : (b : Bin) → binPeanoId (bsuc b) ≡ bsuc (binPeanoId b)
binPeanoIdSuc b rewrite binNattySuc b = refl

-- Follows exactly the uncollapsed natPeanoIdId.
binPeanoIdId : (b : Bin) → binPeanoId b ≡ b
binPeanoIdId = binPeano (λ b → binPeanoId b ≡ b) refl (λ b ih → trans (binPeanoIdSuc b) (cong bsuc ih))

-- We can also follow the direct proof of natPeanoIdId''
-- However we need to rewrite the goal of subst using another subst which my brain can't quite handle now.
{-
binPeanoIdId' : (b : Bin) → binPeanoId b ≡ b
binPeanoIdId' b = {!!}
-}
