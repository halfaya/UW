module Iso where

data _≡_ {ℓ} {A : Set ℓ} (a : A) : A → Set where
  refl : a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}

infix 4 _≅_

record Iso (A : Set) (B : Set) : Set where
  constructor _≅_
  field 
    aToB : A → B
    bToA : B → A
    inv1 : {a : A} → bToA (aToB a) ≡ a
    inv2 : {b : B} → aToB (bToA b) ≡ b
