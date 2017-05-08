module Examples where

open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_×_; _,_)

sumOne : {A B : Set} → A → A ⊎ B
sumOne A = inj₁ A

sumTwo : {A B : Set} → B → A ⊎ B
sumTwo B = inj₂ B

-- note that [_,_] corresponds to Coq sum_rect
sumOneToSumTwo : {A B : Set} → A ⊎ B → B ⊎ A
sumOneToSumTwo = [ inj₂ , inj₁ ]

sumOneToSumTwoMatch : {A B : Set} → A ⊎ B → B ⊎ A
sumOneToSumTwoMatch (inj₁ x) = inj₂ x
sumOneToSumTwoMatch (inj₂ y) = inj₁ y

infix 4 _≤_

data _≤_ (m : ℕ) : ℕ → Set where
  ≤refl : m ≤ m
  ≤suc  : {n : ℕ} → m ≤ n → m ≤ suc n

productOne : {n : ℕ} → n ≡ 1 × n ≤ 1 → n ≡ 1
productOne (a , b) = a

productTwo : {n : ℕ} → n ≡ 1 × n ≤ 1 → n ≤ 1
productTwo (a , b) = b

productThree : {n : ℕ} → n ≡ 1 → n ≤ 1
productThree refl = ≤refl
