{-# OPTIONS --cubical --safe #-}

module Test where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Agda.Builtin.List
open import Data.Vec

-- Strangely even though Σ-eq₂ is defined in the paper, I can't find
-- either of these in the Cubical library, so I'm defining them here.
Σ-eq₁ : {a b : Level} {A : Set a} {B : A → Set b} {p q : Σ A B} → (p ≡ q) →
  fst p ≡ fst q
Σ-eq₁ = cong fst

Σ-eq₂ : {a b : Level} {A : Set a} {B : A → Set b} {p q : Σ A B} → (e : p ≡ q) →
  PathP (λ i → B (fst (e i))) (snd p) (snd q)
Σ-eq₂ = cong snd

module _ {ℓ} {A : Type ℓ} where

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

  List≃Vec : List A ≃ Σ ℕ (Vec A)
  List≃Vec = isoToEquiv (iso List→Vec Vec→List Vec→List→Vec List→Vec→List)

  List≡Vec : List A ≡ Σ ℕ (Vec A)
  List≡Vec = ua List≃Vec
