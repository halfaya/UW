module Test where

open import Data.Nat
open import Data.List

f : ℕ → ℕ → ℕ
f a zero = 0
f a (suc zero) = a
f a (suc (suc b)) = f a (suc b) + f (a + (suc b)) 1

a = map (λ x → f x x) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ [])
