{-# OPTIONS --cubical --safe #-}

module Fin where

open import Cubical.Core.Everything using (_≡_; Level; Type; Type₀; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude     using (refl; sym; _∙_; cong; transport; subst; funExt; transp; I; i0; i1)
open import Cubical.Foundations.Function    using (_∘_)
open import Cubical.Foundations.Isomorphism using (iso; Iso; isoToPath; section; retract)

open import Data.Fin using (Fin; toℕ; fromℕ<; #_; _≟_) renaming (zero to fz; suc to fs)
open import Data.Nat using (ℕ; zero; suc; _<_; z≤n; s≤s)

record Fin1 (n : ℕ) : Type₀ where
  constructor fin1
  field
    r   : ℕ
    r<n : r < n

fin1suc : {n : ℕ} → Fin1 n → Fin1 (suc n)
fin1suc (fin1 r r<n) = fin1 (suc r) (s≤s r<n) 
    
fin→1 : {n : ℕ} → Fin n → Fin1 n
fin→1 fz     = fin1 0 (s≤s z≤n)
fin→1 (fs x) = let fin1 r r<n = fin→1 x in fin1 (suc r) (s≤s r<n)

1→fin : {n : ℕ} → Fin1 n → Fin n
1→fin (fin1 _ r<n) = fromℕ< r<n

fin→1→fin : {n : ℕ} → (r : Fin n) → (1→fin ∘ fin→1) r ≡ r
fin→1→fin fz     = refl
fin→1→fin (fs r) = cong fs (fin→1→fin r)

1→fin→1 : {n : ℕ} → (r : Fin1 n) → (fin→1 ∘ 1→fin) r ≡ r
1→fin→1 (fin1 zero    (s≤s z≤n))       = refl
1→fin→1 (fin1 (suc r) (s≤s (s≤s r<n))) = cong fin1suc (1→fin→1 (fin1 r (s≤s r<n)))
  
fin≃1 : {n : ℕ} → Iso (Fin n) (Fin1 n)
fin≃1 = iso fin→1 1→fin 1→fin→1 fin→1→fin

fin≡1 : {n : ℕ} → Fin n ≡ Fin1 n
fin≡1 = isoToPath fin≃1
