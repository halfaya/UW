{-# OPTIONS --cubical --safe #-}

module ListVec where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude using (refl; sym; _∙_; cong; transport; subst; funExt; transp; I; i0; i1)
--open import Cubical.Foundations.Equiv using (isoToEquiv)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Isomorphism using (iso; Iso; isoToPath; section; retract; isoToEquiv)

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

-----------

-- General theorem that an isomorphism between a type and a dependent pair
-- gives rise to an isomorphism between the second element of the pair
-- and the the original type paired with the appropriate index.
aaa : {ι ℓ ℓ′ : Level}{J : Type ι}(A : Type ℓ)(B : J → Type ℓ′) →
      (e : Iso A (Σ J B)) →
      {j : J} → Iso (B j) (Σ A (λ a → (fst ∘ Iso.fun e) a ≡ j))
aaa A B (iso fun inv rightInv leftInv) {j}
  = iso
      (λ b → inv (j , b) , cong fst (rightInv (j , b)))
      (λ ae → subst B (snd ae) ((snd ∘ fun ∘ fst) ae))
      sec
      ret
  where
    sec : (b : Σ A (λ a → fst (fun a) ≡ j)) →
          (inv (j , transport (λ i → B (snd b i)) (snd (fun (fst b)))) , (λ i → fst (rightInv (j , transport (λ i → B (snd b i)) (snd (fun (fst b)))) i))) ≡ b
    sec = {!!}
    ret : (b : B j) → transport (λ i → B (fst (rightInv (j , b) i))) (snd (fun (inv (j , b)))) ≡ b
    ret b = {!let x = subst (transport (λ i → B (fst (rightInv (j , b) i))) (snd (fun (inv (j , b)))) ≡ b)!}

-- Specialization of aaa to List and Vec.
bbb : {ℓ : Level}{A : Type ℓ} →
      (e : Iso (List A) (Σ ℕ (Vec A))) → {n : ℕ} → Iso (Vec A n) (Σ (List A) (λ xs → (fst ∘ Iso.fun e) xs ≡ n))
bbb {A = A} = aaa (List A) (Vec A)

-- Apply bbb to the first isomorphism to get the second one.
ccc : {ℓ : Level}{A : Type ℓ}{n : ℕ} → Iso (Vec A n) (Σ (List A) (λ xs → (fst ∘ List→Vec) xs ≡ n))
ccc = bbb isoListVec

-- For all lists, the index of the corresponding vector is the length of the list.
len= : {ℓ : Level}{A : Type ℓ} → (xs : List A) → (fst ∘ List→Vec) xs ≡ length xs
len= []       = refl
len= (x ∷ xs) = cong suc (len= xs)

-- Expressing len= as an equivalence of functions.
len≡ : {ℓ : Level}{A : Type ℓ} → fst ∘ List→Vec {ℓ} {A} ≡ length
len≡ = funExt len=

-- Rewrite ccc using length.
-- Could possibly prove this without funExt, but it's very simple with funExt.
ddd : {ℓ : Level}{A : Type ℓ}{n : ℕ} → Iso (Vec A n) (Σ (List A) (λ xs → length xs ≡ n))
ddd {ℓ} {A} {n} = subst (λ (f : List A → ℕ) → Iso (Vec A n) (Σ (List A) (λ xs → f xs ≡ n))) len≡ ccc

-- Equivalence of a vector with a list paired with a proof that its length is the vector index.
-- Note that the type is identical to Vec≡List in ListVec2.agda
Vec≡List' : {ℓ : Level}{A : Type ℓ}{n : ℕ} → Vec A n ≡ Σ (List A) (λ xs → length xs ≡ n)
Vec≡List' = isoToPath ddd
