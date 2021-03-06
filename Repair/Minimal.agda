module Minimal where

open import Data.Bool
open import Data.List
open import Data.List.Properties
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

max : ℕ → ℕ → ℕ
max zero    b       = b
max (suc a) zero    = suc a
max (suc a) (suc b) = suc (max a b)

leMaxR : (k n : ℕ) → n ≤ max k n
leMaxR k       zero    = z≤n
leMaxR zero    (suc n) = s≤s (leMaxR zero n)
leMaxR (suc k) (suc n) = s≤s (leMaxR k n)

lem : (k m n : ℕ) → m ≤ n → k + m ≤ k + n
lem zero m n p    = p
lem (suc k) m n p = s≤s (lem k m n p)

lePlusTrans : (k m n : ℕ) → k ≤ m → k ≤ m + n
lePlusTrans k m zero p rewrite +-right-identity m = p
lePlusTrans k m (suc n) p = 
  let a : k ≤ m + n         ; a = lePlusTrans k m n p
      b : n ≤ suc n         ; b = ≤-step (≤-refl {n})
      c : m + n ≤ m + suc n ; c = lem m n (suc n) b
  in ≤-trans a c 

eqInd : {A : Set} → {x y : A} → (P : A → Set) → P x → x ≡ y → P y
eqInd P base refl = base

eqIndR : {A : Set} → {x y : A} → (P : A → Set) → P x → y ≡ x → P y
eqIndR P base refl = base

newMinimal : {k m n : ℕ} → (H : m ≡ n) → n ≤ max k m
newMinimal {k} {m} {n} H = eqIndR (λ x → n ≤ max k x) (leMaxR k n) H

oldMinimal : {k m n : ℕ} → (H : m ≡ n) → n ≤ max k m + 1
oldMinimal {k} {m} {n} H = eqIndR (λ x → n ≤ max k x + 1) (lePlusTrans n (max k n) 1 (leMaxR k n)) H

oldMinimal' : {k m n : ℕ} → (H : m ≡ n) → n ≤ max k m + 1
oldMinimal' {k} {m} {n} H = lePlusTrans n (max k m) 1 (eqIndR (λ x → n ≤ max k x) (leMaxR k n) H)

addSucL : (m n : ℕ) → suc m + n ≡ suc (m + n)
addSucL _ _ = refl

addSucR : (m n : ℕ) → m + suc n ≡ suc (m + n)
addSucR zero    _ = refl
addSucR (suc m) n = cong suc (addSucR m n)

n<Sn+m→n<n+Sm : (n m : ℕ) → n < suc n + m → n < n + suc m
--n<Sn+m→n<n+Sm n m p = eqIndR (λ x → n < x) (eqInd (λ x → n < x) p (addSucL n m)) (addSucR n m)
n<Sn+m→n<n+Sm n m p = eqIndR (λ x → n < x) p (addSucR n m)

n<n+Sm→n<Sn+m : (n m : ℕ) → n < n + suc m → n < suc n + m
--n<n+Sm→n<Sn+m n m p = eqIndR (λ x → n < x) (eqInd (λ x → n < x) p (addSucR n m)) (addSucL n m)
n<n+Sm→n<Sn+m n m p = eqInd (λ x → n < x) p (addSucR n m)

-- Note an identical proof works for all three cases:
-- n < suc n + m
-- n < suc (n + m)
-- n < n + suc m
n<n+Sm : (n m : ℕ) → n < n + suc m
n<n+Sm zero    m = s≤s z≤n
n<n+Sm (suc n) m = s≤s (n<n+Sm n m)
