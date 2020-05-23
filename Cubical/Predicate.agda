{-# OPTIONS --cubical --safe #-}

module Predicate where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude     using (refl; sym; _∙_; cong; transport; subst; funExt; transp; I; i0; i1)
open import Cubical.Foundations.Function    using (_∘_)
open import Cubical.Foundations.Univalence  using (ua)
open import Cubical.Foundations.Isomorphism using (iso; Iso; isoToPath; section; retract)

open import Data.Bool using (Bool; true; false)
open import Data.Nat  using (ℕ; zero; suc; _>_; s≤s; z≤n; _≤_; _+_)

open import Relation.Unary

{-
First define a predicate as P : A → Bool.
-}

ΣAP≡ΣAQ : (A : Set) → (P Q : A → Bool) → (P ≡ Q) →
  Σ A (λ a → P a ≡ true) ≡ Σ A (λ a → Q a ≡ true)
ΣAP≡ΣAQ A P Q p = subst (λ x → Σ A (λ a → P a ≡ true) ≡ Σ A (λ a → x a ≡ true)) p refl

----------------------

data Pos : Set where
  one : Pos
  suc : Pos → Pos

pos : ℕ → Bool
pos zero    = false
pos (suc _) = true

ℕPos : Set
ℕPos = Σ ℕ (λ n → pos n ≡ true)

ℕ→Pos : ℕ → Pos
ℕ→Pos zero    = one
ℕ→Pos (suc n) = suc (ℕ→Pos n)

Pos→ℕ : Pos → ℕ
Pos→ℕ one     = zero
Pos→ℕ (suc n) = suc (Pos→ℕ n)

ℕ→Pos→ℕ : (n : ℕ) → Pos→ℕ (ℕ→Pos n) ≡ n
ℕ→Pos→ℕ zero    = refl
ℕ→Pos→ℕ (suc n) = cong suc (ℕ→Pos→ℕ n)

Pos→ℕ→Pos : (n : Pos) → ℕ→Pos (Pos→ℕ n) ≡ n
Pos→ℕ→Pos one     = refl
Pos→ℕ→Pos (suc n) = cong suc (Pos→ℕ→Pos n)

Pos→ℕPos : Pos → ℕPos
Pos→ℕPos n = suc (Pos→ℕ n) , refl

ℕPos→Pos : ℕPos → Pos
ℕPos→Pos (zero  , _) = one -- TODO: fix
ℕPos→Pos (suc n , _) = ℕ→Pos n

Pos→ℕPos→Pos : (n : Pos) → ℕPos→Pos (Pos→ℕPos n) ≡ n
Pos→ℕPos→Pos = Pos→ℕ→Pos

ℕPos→Pos→ℕPos : (n : ℕPos) → Pos→ℕPos (ℕPos→Pos n) ≡ n
ℕPos→Pos→ℕPos (zero  , x) = {!!}
ℕPos→Pos→ℕPos (suc n , x) = {!!} --subst {!(λ y → (suc y , ?) ≡ (suc n , x))!} (sym (ℕ→Pos→ℕ n)) refl
--  subst (λ y → (suc y , x) ≡ (suc n , x)) (sym (ℕ→Pos→ℕ n)) refl

isoPosℕPos : Iso Pos ℕPos
isoPosℕPos = iso Pos→ℕPos ℕPos→Pos ℕPos→Pos→ℕPos Pos→ℕPos→Pos

Pos≡ℕPos : Pos ≡ ℕPos
Pos≡ℕPos = isoToPath isoPosℕPos
