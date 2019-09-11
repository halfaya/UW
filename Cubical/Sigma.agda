{-# OPTIONS --cubical --safe #-}

module Sigma where

open import Cubical.Foundations.Prelude

-- Strangely even though Σ-eq₂ is defined in the paper, I can't find
-- either of these in the Cubical library, so I'm defining them here.
Σ-eq₁ : {a b : Level} {A : Set a} {B : A → Set b} {p q : Σ A B} → (p ≡ q) →
  fst p ≡ fst q
Σ-eq₁ = cong fst

Σ-eq₂ : {a b : Level} {A : Set a} {B : A → Set b} {p q : Σ A B} → (e : p ≡ q) →
  PathP (λ i → B (fst (e i))) (snd p) (snd q)
Σ-eq₂ = cong snd

