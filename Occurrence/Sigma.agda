module Sigma where

open import Level using (_⊔_)

-- definition in Agda standard library
{-
record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
-}

infixr 4 _,_

-- implementation as a inductive data type using only Π types
data Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  _,_ : (a : A) → (b : B a) → Σ A B

proj₁ : {A : Set} {B : A → Set} → Σ A B → A
proj₁ (a , _) = a

proj₂ : {A : Set} {B : A → Set} → (p : Σ A B) → B (proj₁ p)
proj₂ (_ , b) = b
