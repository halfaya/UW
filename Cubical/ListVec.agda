{-# OPTIONS --cubical --safe #-}

module ListVec where

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

private
  variable
    ℓ : Level
    A B C : Type ℓ

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

Vec≡List : {ℓ : Level}{A : Type ℓ} → Σ ℕ (Vec A) ≡ List A
Vec≡List {ℓ} {A} i = List≡Vec {ℓ} {A} (~ i)

-- Alternative direct proof without going through equivalences
List≡Vec' : List A ≡ Σ ℕ (Vec A)
List≡Vec' = isoToPath (iso List→Vec Vec→List Vec→List→Vec List→Vec→List)

----------------------------

-- Zip

-- The standard library defines zip using zipWith, so we hide them and redefine them here.
zip : List A → List B → List (A × B)
zip []       _        = []
zip (_ ∷ _)  []       = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys

zipWith : (A → B → C) → List A → List B → List C
zipWith f []       _        = []
zipWith f (_ ∷ _)  []       = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

zipWithPair≡zip : (la : List A)(lb : List B) → zipWith (_,_) la lb ≡ zip la lb
zipWithPair≡zip []       _        = refl
zipWithPair≡zip (_ ∷ _)  []       = refl
zipWithPair≡zip (x ∷ xs) (y ∷ ys) = cong ((x , y) ∷_) (zipWithPair≡zip xs ys)

-- Lift to packed vector
zipV : Σ ℕ (Vec A) → Σ ℕ (Vec B) → Σ ℕ (Vec (A × B))
zipV {ℓ} {A} {ℓ'} {B} = transport (λ i → List≡Vec {A = A} i → List≡Vec {A = B} i → List≡Vec {A = (A × B)} i) zip

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

--v1' : Σ ℕ (Vec ℕ)
--v1' = transport (λ i → List≡Vec i) l1
{-
transp (λ i → Σ ℕ (Vec ℕ)) i0 (3 , 1 ∷ 2 ∷ 3 ∷ [])

transport : {A B : Type ℓ} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a
-}

l1' : List ℕ
l1' = transport Vec≡List v1

l1≡v1 : transport List≡Vec l1 ≡ v1
l1≡v1 = {!refl!}

v3normalForm : v3 ≡ (2 , (1 , 4) ∷ (2 , 5) ∷ [])
v3normalForm = {!!}

v3fst : fst v3 ≡ 2
v3fst = {!!}

----------------------------

-- Derivation of Vector Zip

min : ℕ → ℕ → ℕ
min zero    _       = zero
min (suc _) zero    = zero
min (suc m) (suc n) = suc (min m n)

NonZero : ℕ → Set
NonZero zero    = ⊥
NonZero (suc n) = ⊤

1+n≢0 : {n : ℕ} → suc n ≡ 0 → ⊥
1+n≢0 p = subst NonZero p tt

lengthSuc : {n : ℕ}(a : A)(as : List A) → length as ≡ n → length (a ∷ as) ≡ suc n
lengthSuc {n = zero}  _ []       p = refl
lengthSuc {n = zero}  _ (x ∷ as) p = ⊥-elim (1+n≢0 p) 
lengthSuc {n = suc n} _ as       p = cong suc p

zipMin : (a : List A) → (b : List B) → length (zip a b) ≡ min (length a) (length b)
zipMin []       _        = refl
zipMin (_ ∷ _)  []       = refl
zipMin (x ∷ xs) (y ∷ ys) = lengthSuc (x , y) (zip xs ys) (zipMin xs ys)

----------------------------

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true  = false
not false = true

notnot : (b : Bool) → not (not b) ≡ b
notnot true  = refl
notnot false = refl

--x : Bool ≡ Bool
--x = isoToPath (iso not not notnot notnot)

{-
λ i →
  primGlue Bool
  (λ .x₁ →
     (λ { (i = i0)
            → Bool , not , isoToIsEquiv (iso not not notnot notnot)
        ; (i = i1)
            → Bool ,
              (λ x₂ → x₂) ,
              record
              { equiv-proof =
                  λ y →
                    (y , (λ _ → y)) ,
                    (λ z i₁ → z .snd (~ i₁) , (λ j → z .snd (~ i₁ ∨ j)))
              }
        })
     _ .fst)
  (λ .x₁ →
     (λ { (i = i0)
            → Bool , not , isoToIsEquiv (iso not not notnot notnot)
        ; (i = i1)
            → Bool ,
              (λ x₂ → x₂) ,
              record
              { equiv-proof =
                  λ y →
                    (y , (λ _ → y)) ,
                    (λ z i₁ → z .snd (~ i₁) , (λ j → z .snd (~ i₁ ∨ j)))
              }
        })
     _ .snd)
-}
