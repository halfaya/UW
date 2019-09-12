{-# OPTIONS --safe #-}

module ListVecNonCubical where

open import Agda.Builtin.Sigma
open import Agda.Primitive using (Level)

open import Data.List
open import Data.Nat
open import Data.Vec

open import Relation.Binary.PropositionalEquality

private
  variable
    ℓ : Level
    A B C : Set ℓ

List→Vec : List A → Σ ℕ (Vec A)
List→Vec []       = 0 , []
List→Vec (x ∷ xs) = let (n , ys) = List→Vec xs in (suc n , x ∷ ys)

Vec→List : Σ ℕ (Vec A) → List A
Vec→List (zero  , [])     = []
Vec→List (suc n , x ∷ xs) = x ∷ Vec→List (n , xs)

List→Vec→List : (xs : List A) → Vec→List (List→Vec xs) ≡ xs
List→Vec→List []       = refl
List→Vec→List (x ∷ xs) = cong (x ∷_) (List→Vec→List xs)

Vec→List→Vec : (v : Σ ℕ (Vec A)) → List→Vec (Vec→List v) ≡ v
Vec→List→Vec (zero , [])      = refl
Vec→List→Vec (suc n , x ∷ xs) = cong (λ p → (suc (fst p) , x ∷ snd p)) (Vec→List→Vec (n , xs))
