module Bool where

open import Iso

data Bool : Set where
  true  : Bool
  false : Bool

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data Fin : (n : ℕ) → Set where
  zero : {n : ℕ}         → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

if_then_else : {A : Bool → Set} → (b : Bool) → A true → A false → A b
if true  then c else _ = c
if false then _ else d = d

if_then_else' : {A : Fin 2 → Set} → (b : Fin 2) → A zero → A (suc zero) → A b
if zero           then b else' _ = b
if (suc zero)     then _ else' c = c
if (suc (suc ())) then _ else' _

boolToFin2 : Bool → Fin 2
boolToFin2 true  = zero
boolToFin2 false = suc zero

fin2ToBool : Fin 2 → Bool
fin2ToBool zero    = true
fin2ToBool (suc x) = false

inverse1 : {b : Bool} → fin2ToBool (boolToFin2 b) ≡ b
inverse1 {true}  = refl
inverse1 {false} = refl

inverse2 : {b : Fin 2} → boolToFin2 (fin2ToBool b) ≡ b
inverse2 {zero}     = refl
inverse2 {suc zero} = refl
inverse2 {suc (suc ())}

iso : Iso Bool (Fin 2)
iso = record {aToB = boolToFin2; bToA = fin2ToBool; inv1 = inverse1; inv2 = inverse2}

-- Fin 0 is identical to ⊥
fin0Elim : {A : Set} → Fin 0 → A
fin0Elim ()

---------------------------

idBool : Bool → Bool
idBool x = x

idBool' : Bool → Bool
idBool' true  = true
idBool' false = false

idBool-idBool : {b : Bool} → idBool b ≡ b
idBool-idBool = refl

idBool-idBool' : {b : Bool} → idBool' b ≡ b
--idBool-idBool' = refl -- fails
idBool-idBool' {true}  = refl
idBool-idBool' {false} = refl
