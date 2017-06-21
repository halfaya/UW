{-# OPTIONS --without-K #-}

module J where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat hiding (_<_)

-- J is Coq's eq_rect and J' is eq_rect_r

J : {A : Set} → (x : A) → (P : A → Set) → P x → (y : A) → x ≡ y → P y
J P x px y refl = px

J' : {A : Set} → (x : A) → (P : A → Set) → P x → (y : A) → y ≡ x → P y
J' P x px y refl = px

---------------

infix 4 _≤_ _<_

sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : {A B : Set} → {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong _ refl = refl


data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

_<_ : Nat → Nat → Set 
m < n = suc m ≤ n

n≡n+0 : (n : Nat) → n ≡ n + zero
n≡n+0 zero    = refl
n≡n+0 (suc n) = cong suc (n≡n+0 n)

+-suc : (m n : Nat) → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : (m n : Nat) → m + n ≡ n + m
+-comm zero n    = n≡n+0 n
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

-- 3

≤-trans : {n m p : Nat} → n ≤ m → m ≤ p → n ≤ p
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤o) = s≤s (≤-trans m≤n n≤o)

<transSuc : {n m p : Nat} → n ≤ m → m ≤ p → n < suc p
<transSuc {p = p} a b = s≤s (≤-trans a b)

<transSucPatch : ({n m p : Nat} → n ≤ m → m ≤ p → n ≤ p) →
                 ({n m p : Nat} → n ≤ m → m ≤ p → n < suc p)
<transSucPatch P {n} {m} {p} b c = s≤s (P b c)

<transSuc' : {n m p : Nat} → n ≤ m → m ≤ p → n < suc p
<transSuc' = <transSucPatch ≤-trans

-- 4
<trans+1 : {n m p : Nat} → n ≤ m → m ≤ p → n < p + 1
--<trans+1 {p = p} a b rewrite +-comm p 1 = s≤s (≤-trans a b)
<trans+1 {n = n} {p = p} a b = J (suc p) (λ x → n < x) (s≤s (≤-trans a b)) (p + 1) (+-comm 1 p)

<trans+1Patch : ({n m p : Nat} → n ≤ m → m ≤ p → n < suc p) →
                 ({n m p : Nat} → n ≤ m → m ≤ p → n < p + 1)
--<trans+1Patch P {n} {m} {p} b c rewrite +-comm p 1 = P b c
<trans+1Patch P {n} {m} {p} b c = J (suc p) (λ x → n < x) (P b c) (p + 1) (+-comm 1 p)

<trans+1Patch' : ({n m p : Nat} → n ≤ m → m ≤ p → n < p + 1) →
                 ({n m p : Nat} → n ≤ m → m ≤ p → n < suc p)
--<trans+1Patch' P {n} {m} {p} b c rewrite +-comm 1 p = P b c
<trans+1Patch' P {n} {m} {p} b c = J' (p + 1) (λ x → n < x) (P b c) (suc p) (+-comm 1 p)

-- equivalent:
<trans+1Patch'' : ({n m p : Nat} → n ≤ m → m ≤ p → n < p + 1) →
                 ({n m p : Nat} → n ≤ m → m ≤ p → n < suc p)
<trans+1Patch'' P {n} {m} {p} b c = J (p + 1) (λ x → n < x) (P b c) (suc p) (+-comm p 1)
