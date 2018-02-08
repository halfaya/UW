module Tree where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool
open import Relation.Binary.PropositionalEquality

data Tree : Set where
  leaf : Tree
  node : Tree → Tree → Tree

height : Tree → ℕ
height leaf         = 0
height (node t₁ t₂) = suc (height t₁ ⊔ height t₂)

numLeaves : Tree → ℕ
numLeaves leaf         = 1
numLeaves (node t₁ t₂) = numLeaves t₁ + numLeaves t₂

data Complete : Tree → Set where
  leaf : Complete leaf
  node : {t₁ t₂ : Tree} → Complete t₁ → Complete t₂ → height t₁ ≡ height t₂ → Complete (node t₁ t₂)

completeTreeNumLeaves : (t : Tree) → Complete t → numLeaves t ≡ 2 ^ (height t)
completeTreeNumLeaves leaf         leaf           = refl
completeTreeNumLeaves (node t₁ t₂) (node c₁ c₂ h₁≡h₂) rewrite h₁≡h₂ | ⊔-idem (height t₂) | +-identityʳ (2 ^ height t₂) =
  let a  : numLeaves t₁ ≡ (2 ^ height t₁)                                  ; a  = completeTreeNumLeaves t₁ c₁
      b  : numLeaves t₂ ≡ (2 ^ height t₂)                                  ; b  = completeTreeNumLeaves t₂ c₂
      a' : numLeaves t₁ ≡ (2 ^ height t₂)                                  ; a' = subst (λ n → numLeaves t₁ ≡ 2 ^ n) h₁≡h₂ a
      c  : numLeaves t₁ + numLeaves t₂ ≡ (2 ^ height t₂) + (2 ^ height t₂) ; c = a+b≡c+d a' b
  in c
  where a+b≡c+d : {a b c d : ℕ} → a ≡ c → b ≡ d → a + b ≡ c + d
        a+b≡c+d refl refl = refl


