{-# OPTIONS --rewriting #-}

module Find where

open import Data.Fin using (Fin; zero; toℕ)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Vec
open import Data.Vec.All using (All; _∷_; []) renaming (head to ahead; tail to atail)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- Warm up. Find the maximum element of a non-empty vector and a proof that it is the max.

∈-split : {A : Set} → {a b c : A} → {n : ℕ} → {v : Vec A n} → c ∈ a ∷ v → c ∈ a ∷ b ∷ v
∈-split here      = here
∈-split (there p) = there (there p)

max : {n : ℕ} → (v : Vec ℕ (suc n)) → Σ ℕ (λ k → k ∈ v × All (k ≥_) v)

max (a ∷ []) = (a , (here , ≤-reflexive refl ∷ []))

max (a ∷ b ∷ v) with a ≤? b
max (a ∷ b ∷ v) | yes p = let (c , (e , q)) = max (b ∷ v)
                          in (c , (there e , ≤-trans p (ahead q) ∷ q))
max (a ∷ b ∷ v) | no ¬p = let (c , (e , q)) = max (a ∷ v)
                              b≤a           = ((<⇒≤ ∘ ≰⇒>) ¬p)
                              b≤c           = ≤-trans b≤a (ahead q)
                          in (c , (∈-split e , (ahead q) ∷ b≤c ∷ (atail q)))

-- Obviously not always true, but we'll only use it when okay.
-- This is pretty ugly, so hopefully there's a better way to do this.
postulate
  unsafe+∸ : {m n : ℕ} → m + (n ∸ m) ≡ n

--{-# BUILTIN REWRITE _≡_ #-}
--{-# REWRITE unsafe+∸ #-}

-- Hoare's Find

find : {n : ℕ} → (k : Fin n) → (v : Vec ℕ (suc n)) →
       Σ (Vec ℕ (toℕ k) × ℕ × Vec ℕ (n ∸ (toℕ k))) (λ {(u , (m , w)) → subst (Vec ℕ) (unsafe+∸ {suc (toℕ k)}) (m ∷ (u ++ w)) ≡ v})
find k v = {!!}

find' : (m n : ℕ) → (v : Vec ℕ (suc (m + n))) →
       Σ (Vec ℕ m × ℕ × Vec ℕ n) (λ {(u , (m , w)) → m ∷ (u ++ w) ≡ v})
find' k v = {!!}
