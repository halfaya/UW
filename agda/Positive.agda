{-# OPTIONS --without-K --safe #-}

module Positive where

open import Data.Nat
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

{-
Define positive numbers in a standard way.
Note that n > 0 desugars to 1 ≤ n.
-}

Pos : Set
Pos = Σ ℕ (λ n → n > 0)

psuc : Pos → Pos
psuc (n , s≤s z≤n) = suc n , s≤s z≤n

plus : Pos → Pos → Pos
plus (suc zero    , s≤s z≤n) (suc n , s≤s z≤n) = suc (suc n), s≤s z≤n
plus (suc (suc m) , s≤s z≤n) (suc n , s≤s z≤n) = psuc (plus (suc m , s≤s z≤n) (suc n , s≤s z≤n))

double : Pos → Pos
double (suc zero    , s≤s z≤n) = suc (suc zero) , s≤s z≤n
double (suc (suc m) , s≤s z≤n) = psuc (psuc (double (suc m , s≤s z≤n)))

m+[1+n]=1+[m+n] : (m n : Pos) → plus m (psuc n) ≡ psuc (plus m n)
m+[1+n]=1+[m+n] (suc zero    , s≤s z≤n) (suc n , s≤s z≤n) = refl
m+[1+n]=1+[m+n] (suc (suc m) , s≤s z≤n) (suc n , s≤s z≤n) =
  cong psuc (m+[1+n]=1+[m+n] (suc m , s≤s z≤n) (suc n , s≤s z≤n))

2n=n+n : (n : Pos) → double n ≡ plus n n
2n=n+n (suc zero    , s≤s z≤n) = refl
2n=n+n (suc (suc n) , s≤s z≤n) =
  let a = cong psuc (2n=n+n (suc n , s≤s z≤n))
      b = sym (m+[1+n]=1+[m+n] (suc n , s≤s z≤n) (suc n , s≤s z≤n))
  in cong psuc (trans a b)

-------

doubleℕ : ℕ → ℕ
doubleℕ zero    = zero
doubleℕ (suc n) = suc (suc (doubleℕ n))

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

2n=n+nℕ : (n : ℕ) → doubleℕ n ≡ n + n
2n=n+nℕ zero    = refl
2n=n+nℕ (suc n) =
  let a = cong suc (2n=n+nℕ n)
      b = sym (+-suc n n)
  in cong suc (trans a b)
