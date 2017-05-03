module Number where

open import Data.Bool
open import Data.Empty
open import Data.Nat
open import Data.Nat.Divisibility
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

max2pow : ℕ × ℕ → ℕ × ℕ × ℕ
max2pow (m , n) with 2 ∣? m | 2 ∣? n
... | yes _  | yes _ = {!!}
... | no _   | no _  = {!!}
... | yes _  | no _  = {!!}
... | no _   | yes _ = {!!}
