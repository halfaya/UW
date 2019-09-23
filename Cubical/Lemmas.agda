{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-} -- TODO: Remove this and re-add safe

module Lemmas where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd)

open import Cubical.Foundations.Prelude using (subst; sym; refl; cong)
open import Cubical.Foundations.Isomorphism using (Iso; iso; section; retract)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; length; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)

open import Function using (_∘_)

min : ℕ → ℕ → ℕ
min zero    _       = zero
min (suc _) zero    = zero
min (suc m) (suc n) = suc (min m n)

-- Thanks Andreas for this (subsumed by NoConfusion)
NonZero : ℕ → Set
NonZero zero    = ⊥
NonZero (suc n) = ⊤

-- Thanks Jasper for this.
-- Proves both disjointness and injectivity.
NoConfusion : ℕ → ℕ → Set
NoConfusion zero zero       = ⊤
NoConfusion zero (suc n)    = ⊥
NoConfusion (suc m) zero    = ⊥
NoConfusion (suc m) (suc n) = m ≡ n

1+n≢0 : {n : ℕ} → suc n ≡ 0 → ⊥
1+n≢0 p = subst (λ m → NoConfusion m zero) (sym p) tt
--1+n≢0 p = subst NonZero p tt -- also works

suc-injective : {a b : ℕ} → suc a ≡ suc b → a ≡ b
suc-injective {a = a} e = subst (NoConfusion (suc a)) e refl

minEq : (a b : ℕ) → a ≡ b → min a b ≡ a
minEq zero _ _ = refl
minEq (suc a) zero e = sym e
minEq (suc a) (suc b) e = cong suc (minEq a b (suc-injective e))

-- Use □ instead, but as suggested by Jesper this is another way to define transitivity.
trans : {ℓ : Level}{A : Type ℓ}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans {x = x} x≡y y≡z = subst (x ≡_) y≡z x≡y

------------

aaa : (I A : Set)(B : I → Set) →
      Iso A (Σ I B) →
      Σ (A → I) (λ f → (i : I) → Iso (B i) (Σ A (λ a → f a ≡ i)))
aaa I A B (iso fun inv rightInv leftInv)
  = fst ∘ fun , λ i → iso
      (λ b → inv (i , b) , subst (λ x → fst x ≡ i) (sym (rightInv (i , b))) refl)
      (λ ae → subst B (snd ae) (snd (fun (fst ae))))
      {!!}
      {!!}
