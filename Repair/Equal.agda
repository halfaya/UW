module Equal where

data _≡_ {ℓ} {A : Set ℓ} (a : A) : A → Set where
  refl : a ≡ a

{-
data _≡_ : ∀{ℓ} {A : Set ℓ} → A → A → Set where
  refl : ∀{ℓ} {A : Set ℓ} {a : A} → a ≡ a
  funx : {A : Set}  {B : Set} {f g : A → B} → ((a : A) → f a ≡ g a) → f ≡ g
-}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

ℕ≡Nat : ℕ ≡ Nat
ℕ≡Nat = {!!}
