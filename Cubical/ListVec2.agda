{-# OPTIONS --cubical #-} -- TODO: re-add safe

module ListVec2 where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude using (refl; sym; _□_; cong; transport; subst)
open import Cubical.Foundations.Equiv using (isoToEquiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Isomorphism using (iso; isoToPath)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; length; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc; pred)
open import Data.Product using (_×_)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)

open import Lemmas

Vec→List : {ℓ : Level}{A : Type ℓ}{n : ℕ} → Vec A n → Σ (List A) (λ as → length as ≡ n)
Vec→List []       = [] , refl
Vec→List (x ∷ xs) = let (ys , p) = Vec→List xs in x ∷ ys , cong suc p

List→Vec : {ℓ : Level}{A : Type ℓ}{n : ℕ} → Σ (List A) (λ as → length as ≡ n) → Vec A n
List→Vec {n = zero}  (xs , p)     = []
List→Vec {n = suc n} ([] , p)     = ⊥-elim (1+n≢0 (sym p))
List→Vec {n = suc n} (x ∷ xs , p) = x ∷ List→Vec (xs , cong pred p)

Vec→List→Vec : {ℓ : Level}{A : Type ℓ}{n : ℕ} → (v : Vec A n) → List→Vec (Vec→List v) ≡ v
Vec→List→Vec []       = refl
Vec→List→Vec (x ∷ xs) = let y = Vec→List→Vec in {!!}

List→Vec→List : {ℓ : Level}{A : Type ℓ}{n : ℕ} → (v : Σ (List A) (λ as → length as ≡ n)) → Vec→List (List→Vec v) ≡ v
List→Vec→List {n = zero} ([] , p)      = {!!}
List→Vec→List {n = zero}  (x ∷ xs , p) = ⊥-elim (1+n≢0 p)
List→Vec→List {n = suc n} ([] , p)     = ⊥-elim (1+n≢0 (sym p))
List→Vec→List {n = suc n} (x ∷ xs , p) = {!!}

List≃Vec : {ℓ : Level}{A : Type ℓ}{n : ℕ} → Σ (List A) (λ as → length as ≡ n) ≃ Vec A n
List≃Vec = isoToEquiv (iso List→Vec Vec→List Vec→List→Vec List→Vec→List)

List≡Vec : {ℓ : Level}{A : Type ℓ}{n : ℕ} → Σ (List A) (λ as → length as ≡ n) ≡ Vec A n
List≡Vec = ua List≃Vec

Vec≡List : {ℓ : Level}{A : Type ℓ}{n : ℕ} → Vec A n ≡ Σ (List A) (λ as → length as ≡ n)
Vec≡List {ℓ} {A} {n} i = List≡Vec {ℓ} {A} {n} (~ i)

-- Alternative direct proof without going through equivalences
List≡Vec' : {ℓ : Level}{A : Type ℓ}{n : ℕ} → Σ (List A) (λ as → length as ≡ n) ≡ Vec A n
List≡Vec' = isoToPath (iso List→Vec Vec→List Vec→List→Vec List→Vec→List)
