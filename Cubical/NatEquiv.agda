{-# OPTIONS --cubical --safe #-}

module NatEquiv where

open import Cubical.Core.Everything         using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude     using (refl; sym; _∙_; cong; transport; subst; funExt; transp; I; i0; i1)
open import Cubical.Foundations.Function    using (_∘_)
open import Cubical.Foundations.Univalence  using (ua)
open import Cubical.Foundations.Isomorphism using (iso; Iso; isoToPath; section; retract)

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Nat.Base  using (ℕ; zero; suc)
open import Data.Product   using (_×_; proj₁; proj₂)

record Nat1 : Type where
  constructor nat1
  field
    m   : ℕ
    n   : ℕ
    m=n : m ≡ n

ℕ→Nat1 : ℕ → Nat1
ℕ→Nat1 n = nat1 n n refl

Nat1→ℕ : Nat1 → ℕ
Nat1→ℕ (nat1 m _ _) = m

ℕ→Nat1→ℕ : (n : ℕ) → (Nat1→ℕ ∘ ℕ→Nat1) n ≡ n
ℕ→Nat1→ℕ n = refl

Nat1→ℕ→Nat1 : (n : Nat1) → (ℕ→Nat1 ∘ Nat1→ℕ) n ≡ n
Nat1→ℕ→Nat1 (nat1 m n m=n) i = nat1 m (m=n i) λ j → {!!}

ℕ≅Nat1 : Iso ℕ Nat1
ℕ≅Nat1 = iso ℕ→Nat1 Nat1→ℕ Nat1→ℕ→Nat1 ℕ→Nat1→ℕ

ℕ≡Nat1 : ℕ ≡ Nat1
ℕ≡Nat1 = isoToPath ℕ≅Nat1

