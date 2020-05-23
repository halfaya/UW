{-# OPTIONS --without-K --safe #-}

module Natty where

open import Data.Nat using (ℕ; zero; suc)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

data Bin : Set where
  b0 : Bin         -- 0
  s1 : Bin → Bin   -- 2*n + 1
  s2 : Bin → Bin   -- 2*{n+1}

bsuc : Bin → Bin
bsuc b0     = s1 b0
bsuc (s1 n) = s2 n
bsuc (s2 n) = s1 (bsuc n)

data Natty : Bin → Set where
  n0   : Natty b0
  nsuc : (b : Bin) → Natty b → Natty (bsuc b)

s1Natty : (b : Bin) → Natty b → Natty (s1 b)
s1Natty .b0       n0         = nsuc b0 n0
s1Natty .(bsuc b) (nsuc b n) = nsuc (s2 b) (nsuc (s1 b) (s1Natty b n))

s2Natty : (b : Bin) → Natty b → Natty (s2 b)
s2Natty .b0       n0         = nsuc (s1 b0) (nsuc b0 n0)
s2Natty .(bsuc b) (nsuc b n) = nsuc (s1 (bsuc b)) (nsuc (s2 b) (s2Natty b n))

natty : (b : Bin) → Natty b
natty b0     = n0
natty (s1 b) = s1Natty b (natty b)
natty (s2 b) = s2Natty b (natty b)

natPeano : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
natPeano P p0 psuc zero    = p0
natPeano P p0 psuc (suc n) = psuc n (natPeano P p0 psuc n)

natPeanoId : ℕ → ℕ
natPeanoId = natPeano (λ _ → ℕ) zero (λ _ n → suc n)

natPeanoIdSuc : (n : ℕ) → natPeanoId (suc n) ≡ suc (natPeanoId n)
natPeanoIdSuc n = refl

natPeanoIdId : (n : ℕ) → natPeanoId n ≡ n
natPeanoIdId = natPeano (λ n → natPeanoId n ≡ n) refl (λ n ih → trans (natPeanoIdSuc n) (cong suc ih))

-- Since (natPeanoIdSuc n) is just refl, the proof collapses as follows.
natPeanoIdId' : (n : ℕ) → natPeanoId n ≡ n
natPeanoIdId' = natPeano (λ n → natPeanoId n ≡ n) refl (λ n ih → cong suc ih)

nattyPeano : (P : Bin → Set) → P b0 → ((b : Bin) → P b → P (bsuc b)) → (b : Bin) → Natty b → P b
nattyPeano P p0 psuc .b0       n0         = p0
nattyPeano P p0 psuc .(bsuc b) (nsuc b n) = psuc b (nattyPeano P p0 psuc b n)

binPeano : (P : Bin → Set) → P b0 → ((b : Bin) → P b → P (bsuc b)) → (b : Bin) → P b
binPeano P p0 psuc b = nattyPeano P p0 psuc b (natty b)

binPeanoId : Bin → Bin
binPeanoId = binPeano (λ _ → Bin) b0 (λ _ b → bsuc b)

binPeanoIdSuc : (b : Bin) → binPeanoId (bsuc b) ≡ bsuc (binPeanoId b)
binPeanoIdSuc b = {!!}

-- Follows exactly the uncollapsed natPeanoIdId.
binPeanoIdId : (b : Bin) → binPeanoId b ≡ b
binPeanoIdId = binPeano (λ b → binPeanoId b ≡ b) refl (λ b ih → trans (binPeanoIdSuc b) (cong bsuc ih))
