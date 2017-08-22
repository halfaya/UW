module LeReflect where

open import Data.Nat
open import Data.Nat.Properties
open import Function
open import Relation.Binary.PropositionalEquality

{-
data _≤_ : Rel ℕ Level.zero where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

data _≤′_ (m : ℕ) : ℕ → Set where
  ≤′-refl :                         m ≤′ m
  ≤′-step : ∀ {n} (m≤′n : m ≤′ n) → m ≤′ suc n
-}

-- Conjugation

≤′⇒≤/s≤s : {m n : ℕ} → (x : m ≤′ n) → ≤′⇒≤ (s≤′s x) ≡ s≤s (≤′⇒≤ x)
≤′⇒≤/s≤s ≤′-refl     = refl
≤′⇒≤/s≤s (≤′-step x) = cong ≤-step (≤′⇒≤/s≤s x)

≤⇒≤′/≤-step : {m n : ℕ} → (x : m ≤ n) → ≤⇒≤′ (≤-step x) ≡ ≤′-step (≤⇒≤′ x)
≤⇒≤′/≤-step z≤n     = refl
≤⇒≤′/≤-step (s≤s x) = cong s≤′s (≤⇒≤′/≤-step x)

-- Isomorphism between ≤ and ≤′

≤⇒≤′⇒≤ : {m n : ℕ} → (x : m ≤ n) → ≤′⇒≤ (≤⇒≤′ x) ≡ x
≤⇒≤′⇒≤ {zero}  {zero}  z≤n     = refl
≤⇒≤′⇒≤ {zero}  {suc n} z≤n     = cong ≤-step (≤⇒≤′⇒≤ z≤n)
≤⇒≤′⇒≤ {suc m} {suc n} (s≤s x) rewrite (≤′⇒≤/s≤s (≤⇒≤′ x)) = cong s≤s (≤⇒≤′⇒≤ x)

≤′⇒≤⇒≤′ : {m n : ℕ} → (x : m ≤′ n) → ≤⇒≤′ (≤′⇒≤ x) ≡ x
≤′⇒≤⇒≤′                  (≤′-step x) rewrite (≤⇒≤′/≤-step (≤′⇒≤ x)) = cong ≤′-step (≤′⇒≤⇒≤′ x)
≤′⇒≤⇒≤′ {zero}  {zero}   ≤′-refl     = refl
≤′⇒≤⇒≤′ {suc m} {suc .m} ≤′-refl     = cong s≤′s (≤′⇒≤⇒≤′ {m} {m} ≤′-refl)
