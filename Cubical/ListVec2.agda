{-# OPTIONS --cubical --safe #-}

module ListVec2 where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude using (refl; sym; _□_; cong; transport; subst)
open import Cubical.Foundations.Equiv using (isoToEquiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Isomorphism using (iso; isoToPath)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; length; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_×_)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)

Vec→List : {ℓ : Level}{A : Type ℓ}{n : ℕ} → Vec A n → Σ (List A) (λ a → length a ≡ n)
Vec→List {n = .0} [] = [] , refl
Vec→List {n = .(suc _)} (x ∷ xs) = let (ys , p) = Vec→List xs in x ∷ ys , {!!}

List→Vec : {ℓ : Level}{A : Type ℓ}{n : ℕ} → Σ (List A) (λ a → length a ≡ n) → Vec A n
List→Vec {A = A} ([] , p) = subst (Vec A) p []
List→Vec {n = zero}  (x ∷ xs , p) = {!!}
List→Vec {n = suc n} (x ∷ xs , p) = {!!} --let a = List→Vec (xs , {!!}) in {!!} 

{-
List→Vec→List : {ℓ : Level}{A : Type ℓ} → (xs : List A) → Vec→List (List→Vec xs) ≡ xs
List→Vec→List []       = refl
List→Vec→List (x ∷ xs) = cong (x ∷_) (List→Vec→List xs)

Vec→List→Vec : {ℓ : Level}{A : Type ℓ} → (v : Σ ℕ (Vec A)) → List→Vec (Vec→List v) ≡ v
Vec→List→Vec (zero , [])      = refl
Vec→List→Vec (suc n , x ∷ xs) = cong (λ p → (suc (fst p) , x ∷ snd p)) (Vec→List→Vec (n , xs))

List≃Vec : {ℓ : Level}{A : Type ℓ} → List A ≃ Σ ℕ (Vec A)
List≃Vec = isoToEquiv (iso List→Vec Vec→List Vec→List→Vec List→Vec→List)

List≡Vec : {ℓ : Level}{A : Type ℓ} → List A ≡ Σ ℕ (Vec A)
List≡Vec = ua List≃Vec

Vec≡List : {ℓ : Level}{A : Type ℓ} → Σ ℕ (Vec A) ≡ List A
Vec≡List {ℓ} {A} i = List≡Vec {ℓ} {A} (~ i)

-- Alternative direct proof without going through equivalences
List≡Vec' : {ℓ : Level}{A : Type ℓ} → List A ≡ Σ ℕ (Vec A)
List≡Vec' = isoToPath (iso List→Vec Vec→List Vec→List→Vec List→Vec→List)

----------------------------

-- Zip

-- The standard library defines zip using zipWith, so we hide them and redefine them here.
zip : {ℓ : Level}{A B : Type ℓ} → List A → List B → List (A × B)
zip []       _        = []
zip (_ ∷ _)  []       = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys

zipWith : {ℓ : Level}{A B C : Type ℓ} → (A → B → C) → List A → List B → List C
zipWith f []       _        = []
zipWith f (_ ∷ _)  []       = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

zipWithPair≡zip : {ℓ : Level}{A B : Type ℓ} → (la : List A)(lb : List B) → zipWith (_,_) la lb ≡ zip la lb
zipWithPair≡zip []       _        = refl
zipWithPair≡zip (_ ∷ _)  []       = refl
zipWithPair≡zip (x ∷ xs) (y ∷ ys) = cong ((x , y) ∷_) (zipWithPair≡zip xs ys)

-- Lift to packed vector
zipV : {ℓ : Level}{A B : Type ℓ} → Σ ℕ (Vec A) → Σ ℕ (Vec B) → Σ ℕ (Vec (A × B))
zipV {ℓ} {A} {B} = transport (λ i → List≡Vec {A = A} i → List≡Vec {A = B} i → List≡Vec {A = (A × B)} i) zip

-- Test using concrete data
l1 l2 : List ℕ
l1 = 1 ∷ 2 ∷ 3 ∷ []
l2 = 4 ∷ 5 ∷ []

l3 : List (ℕ × ℕ)
l3 = zip l1 l2

v1 v2 : Σ ℕ (Vec ℕ)
v1 = (3 , 1 ∷ 2 ∷ 3 ∷ [])
v2 = (2 , 4 ∷ 5 ∷ [])

v3 : Σ ℕ (Vec (ℕ × ℕ))
v3 = zipV v1 v2

-- Transport is not implemented yet for indexed inductive types,
-- so the following gets stuck when you try to normalize it.
-- Normal form: transp (λ i → Σ ℕ (Vec ℕ)) i0 (3 , 1 ∷ 2 ∷ 3 ∷ [])

v1' : Σ ℕ (Vec ℕ)
v1' = transport List≡Vec l1
-}
