{-# OPTIONS --cubical --safe #-}

module ListVecZip where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude using (refl; sym; _□_; cong; transport; subst; funExt; transp; I; i0; i1)
open import Cubical.Foundations.Equiv using (isoToEquiv)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Isomorphism using (iso; Iso; isoToPath; section; retract)

open import Data.List using (List; length; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_×_)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)

open import Lemmas
open import ListVec

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

----------------------------

-- Derivation of Vector Zip

zipMin : {ℓ : Level}{A B : Type ℓ} → (a : List A) → (b : List B) → length (zip a b) ≡ min (length a) (length b)
zipMin []       _        = refl
zipMin (_ ∷ _)  []       = refl
zipMin (x ∷ xs) (y ∷ ys) = cong suc (zipMin xs ys)

zipEq : {ℓ : Level}{A B : Type ℓ} → (a : List A) → (b : List B) → length a ≡ length b → length (zip a b) ≡ length a
zipEq  a b e = zipMin a b □ minEq (length a) (length b) e

zipV1 : {ℓ : Level}{A B : Type ℓ}{m n : ℕ} → (a : Vec A m) → (b : Vec B n) → m ≡ n → Vec (A × B) m
zipV1             []       _  _       = []
zipV1 {_} {A} {B} (_ ∷ _)  [] e       = subst (Vec (A × B)) (sym e) []
zipV1             (a ∷ as) (b ∷ bs) e = (a , b) ∷ zipV1 as bs (suc-injective e)

--zipV1 : {ℓ : Level}{A B : Type ℓ}{m n : ℕ} → (a : Vec A m) → (b : Vec B n) → m ≡ length b → length (zip a b) ≡ length a
