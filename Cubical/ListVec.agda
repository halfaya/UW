{-# OPTIONS --cubical --safe #-}

module ListVec where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude using (refl; sym; _□_; cong; transport; subst; funExt; transp; i0; i1)
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

List→Vec : {ℓ : Level}{A : Type ℓ} → List A → Σ ℕ (Vec A)
List→Vec []       = 0 , []
List→Vec (x ∷ xs) = let (n , ys) = List→Vec xs in (suc n , x ∷ ys)

Vec→List : {ℓ : Level}{A : Type ℓ} → Σ ℕ (Vec A) → List A
Vec→List (zero  , [])     = []
Vec→List (suc n , x ∷ xs) = x ∷ Vec→List (n , xs)

List→Vec→List : {ℓ : Level}{A : Type ℓ} → (xs : List A) → Vec→List (List→Vec xs) ≡ xs
List→Vec→List []       = refl
List→Vec→List (x ∷ xs) = cong (x ∷_) (List→Vec→List xs)

Vec→List→Vec : {ℓ : Level}{A : Type ℓ} → (v : Σ ℕ (Vec A)) → List→Vec (Vec→List v) ≡ v
Vec→List→Vec (zero , [])      = refl
Vec→List→Vec (suc n , x ∷ xs) = cong (λ p → (suc (fst p) , x ∷ snd p)) (Vec→List→Vec (n , xs))

isoListVec : {ℓ : Level}{A : Type ℓ} → Iso (List A) (Σ ℕ (Vec A))
isoListVec = iso List→Vec Vec→List Vec→List→Vec List→Vec→List

List≃Vec : {ℓ : Level}{A : Type ℓ} → List A ≃ Σ ℕ (Vec A)
List≃Vec = isoToEquiv isoListVec

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

-----------



aaa : {ι ℓ ℓ′ : Level}{I : Type ι}(A : Type ℓ)(B : I → Type ℓ′) →
      (e : Iso A (Σ I B)) →
      {i : I} → Iso (B i) (Σ A (λ a → (fst ∘ Iso.fun e) a ≡ i))
aaa A B (iso fun inv rightInv leftInv) {i}
  = iso
      (λ b → inv (i , b) , subst (λ x → fst x ≡ i) (sym (rightInv (i , b))) refl)
      (λ ae → subst B (snd ae) ((snd ∘ fun ∘ fst) ae))
      sec
      ret
  where
    sec : (ae : Σ A (λ a → fst (fun a) ≡ i)) → 
          (inv (i , subst B (snd ae) (snd (fun (fst ae)))) ,
           subst (λ x → fst x ≡ i) (sym (rightInv (i , subst B (snd ae) (snd (fun (fst ae)))))) refl) ≡ ae
    sec (a , e) = {!!}
    ret : retract
            (λ b →
              inv (i , b) ,
              subst (λ x → fst x ≡ i) (λ i₁ → rightInv (i , b) (~ i₁)) (λ _ → i))
            (λ ae → subst B (snd ae) (snd (fun (fst ae))))
--    ret : (b : B i) → subst B (snd (inv (i , b) , subst (λ x → fst x ≡ i) (sym (rightInv (i , b))) refl))
--                      ((snd ∘ fun ∘ fst) (inv (i , b) , subst (λ x → fst x ≡ i) (sym (rightInv (i , b))) refl)) ≡ b
    ret = {!!}

bbb : {ℓ : Level}{A : Type ℓ} →
      (e : Iso (List A) (Σ ℕ (Vec A))) → {n : ℕ} → Iso (Vec A n) (Σ (List A) (λ xs → (fst ∘ Iso.fun e) xs ≡ n))
bbb {A = A} = aaa (List A) (Vec A)

ccc : {ℓ : Level}{A : Type ℓ}{n : ℕ} → Iso (Vec A n) (Σ (List A) (λ xs → (fst ∘ List→Vec) xs ≡ n))
ccc = bbb isoListVec

len= : {ℓ : Level}{A : Type ℓ} → (xs : List A) → (fst ∘ List→Vec) xs ≡ length xs
len= []       = refl
len= (x ∷ xs) = cong suc (len= xs)

len≡ : {ℓ : Level}{A : Type ℓ} → fst ∘ List→Vec {ℓ} {A} ≡ length
len≡ = funExt len=

-- Could possibly prove this without funExt
ddd : {ℓ : Level}{A : Type ℓ}{n : ℕ} → Iso (Vec A n) (Σ (List A) (λ xs → length xs ≡ n))
ddd {ℓ} {A} {n} = subst (λ (f : List A → ℕ) → Iso (Vec A n) (Σ (List A) (λ xs → f xs ≡ n))) len≡ ccc

-- Type is identical to Vec≡List in ListVec2.agda
Vec≡List' : {ℓ : Level}{A : Type ℓ}{n : ℕ} → Vec A n ≡ Σ (List A) (λ xs → length xs ≡ n)
Vec≡List' = isoToPath ddd
