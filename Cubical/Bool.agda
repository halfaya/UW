{-# OPTIONS --cubical --safe #-}

module Bool where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism


data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true  = false
not false = true

notnot : (b : Bool) → not (not b) ≡ b
notnot true  = refl
notnot false = refl

x : Bool ≡ Bool
x = isoToPath (iso not not notnot notnot)

{-
λ i →
  primGlue Bool
  (λ .x₁ →
     (λ { (i = i0)
            → Bool , not , isoToIsEquiv (iso not not notnot notnot)
        ; (i = i1)
            → Bool ,
              (λ x₂ → x₂) ,
              record
              { equiv-proof =
                  λ y →
                    (y , (λ _ → y)) ,
                    (λ z i₁ → z .snd (~ i₁) , (λ j → z .snd (~ i₁ ∨ j)))
              }
        })
     _ .fst)
  (λ .x₁ →
     (λ { (i = i0)
            → Bool , not , isoToIsEquiv (iso not not notnot notnot)
        ; (i = i1)
            → Bool ,
              (λ x₂ → x₂) ,
              record
              { equiv-proof =
                  λ y →
                    (y , (λ _ → y)) ,
                    (λ z i₁ → z .snd (~ i₁) , (λ j → z .snd (~ i₁ ∨ j)))
              }
        })
     _ .snd)
-}
