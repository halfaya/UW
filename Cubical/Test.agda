{-# OPTIONS --cubical --safe #-}

module Test where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Agda.Builtin.List
open import Data.Vec

module _ {ℓ} {A : Type ℓ} where

  List→Vec : List A → Σ ℕ (λ n → Vec A n)
  List→Vec [] = 0 , []
  List→Vec (x ∷ xs) = let (n , ys) = List→Vec xs in (suc n , x ∷ ys)

  Vec→List : Σ ℕ (λ n → Vec A n) → List A
  Vec→List (zero  , [])     = []
  Vec→List (suc n , x ∷ xs) = x ∷ Vec→List (n , xs)

  List→Vec→List : (xs : List A) → Vec→List (List→Vec xs) ≡ xs
  List→Vec→List []       = refl
  List→Vec→List (x ∷ xs) = {!!}

  Vec→List→Vec : (v : Σ ℕ (λ n → Vec A n)) → List→Vec (Vec→List v) ≡ v
  Vec→List→Vec (zero , [])      = refl
  Vec→List→Vec (suc n , x ∷ xs) = {!!}

  List≃Vec : List A ≃ Σ ℕ (λ n → Vec A n)
  List≃Vec = isoToEquiv (iso List→Vec Vec→List Vec→List→Vec List→Vec→List)

  List≡Vec : List A ≡ Σ ℕ (λ n → Vec A n)
  List≡Vec = ua List≃Vec
