{-# OPTIONS --cubical --safe #-}

module MinTest where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base
open import Data.List hiding (zip; zipWith)
open import Data.Product using (_×_)
open import Data.Unit using (⊤; tt)
open import Data.Vec hiding (zip; zipWith)

List→Vec : {ℓ : Level}{A : Type ℓ} → List A → Σ ℕ (Vec A)
List→Vec []       = 0 , []
List→Vec (x ∷ xs) = let (n , ys) = List→Vec xs in (suc n , x ∷ ys)

Vec→List : {ℓ : Level}{A : Type ℓ} → Σ ℕ (Vec A) → List A
Vec→List (zero  , [])     = []
Vec→List (suc n , x ∷ xs) = x ∷ Vec→List (n , xs)

List→Vec→List : {ℓ : Level} {A : Type ℓ} → (xs : List A) → Vec→List (List→Vec xs) ≡ xs
List→Vec→List []       = refl
List→Vec→List (x ∷ xs) = cong (x ∷_) (List→Vec→List xs)

Vec→List→Vec : {ℓ : Level}{A : Type ℓ} → (v : Σ ℕ (Vec A)) → List→Vec (Vec→List v) ≡ v
Vec→List→Vec (zero , [])      = refl
Vec→List→Vec (suc n , x ∷ xs) = cong (λ p → (suc (fst p) , x ∷ snd p)) (Vec→List→Vec (n , xs))

List≃Vec : {ℓ : Level} {A : Type ℓ} → List A ≃ Σ ℕ (Vec A)
List≃Vec = isoToEquiv (iso List→Vec Vec→List Vec→List→Vec List→Vec→List)

List≡Vec : {ℓ : Level}{A : Type ℓ} → List A ≡ Σ ℕ (Vec A)
List≡Vec = ua List≃Vec

Vec≡List : {ℓ : Level}{A : Type ℓ} → Σ ℕ (Vec A) ≡ List A
Vec≡List {ℓ} {A} i = List≡Vec {ℓ} {A} (~ i)

-- Alternative direct proof without going through equivalences
List≡Vec' : {ℓ : Level} {A : Type ℓ} → List A ≡ Σ ℕ (Vec A)
List≡Vec' = isoToPath (iso List→Vec Vec→List Vec→List→Vec List→Vec→List)

----------------------------

l1 : List ℕ
l1 = 1 ∷ 2 ∷ []

v1 : Σ ℕ (Vec ℕ)
v1 = (2 , 1 ∷ 2 ∷ [])

l1≡v1 : transport List≡Vec l1 ≡ v1
l1≡v1 = {!refl!}

{-
Trying to fill the hole above with refl gives the following error:

transp
(λ i → Vec ℕ (transp (λ i₁ → ℕ) (i0 ∨ ~ i) (fst (prim^unglue l1))))
i0 (1 ∷ snd (List→Vec (2 ∷ [])))
!= 1 ∷ 2 ∷ [] of type
Vec ℕ (fst (transp (λ i → Σ ℕ (Vec ℕ)) i0 (prim^unglue l1)))
when checking that the expression refl has type
transport List≡Vec l1 ≡ v1
-}

v2 : Σ ℕ (Vec ℕ)
v2 = transport List≡Vec l1
{- Normal form is
transp (λ i → Σ ℕ (Vec ℕ)) i0 (2 , 1 ∷ 2 ∷ [])
-}

v2fst : ℕ
v2fst = fst v2
{- Normal form is
2
-}

v2snd : Vec ℕ 2
v2snd = snd v2
{- Normal form is
transp (λ i → Vec ℕ 2) i0 (1 ∷ 2 ∷ [])
-}

