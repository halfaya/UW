module Sort where

open import Data.Bool
open import Data.List
open import Data.List.Properties
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

-- return the nth element of a list, or the default if there is no nth element
nth : {A : Set} → ℕ → List A → A → A
nth _       []       default = default
nth zero    (x ∷ xs) default = x
nth (suc n) (x ∷ xs) default = nth n xs default

data Sorted : List ℕ → Set where
  sortedNil  : Sorted []
  sorted1    : {n : ℕ} → Sorted (n ∷ [])
  sortedCons : {m n : ℕ} → {l : List ℕ} → m ≤ n → Sorted (n ∷ l) → Sorted (m ∷ n ∷ l)

Sorted' : List ℕ → Set
Sorted' l = {i j : ℕ} → {p : i < j} → {q : j < length l} → nth i l 0 ≤ nth j l 0

Sorted→Sorted' : {l : List ℕ} → Sorted l → Sorted' l
Sorted→Sorted' sortedNil        = z≤n
Sorted→Sorted' sorted1          {i} {j} {p} {q} = {!!}
Sorted→Sorted' (sortedCons x p) = let z = Sorted→Sorted' p in {!!}

Sorted'→Sorted : {l : List ℕ} → Sorted' l → Sorted l
Sorted'→Sorted {[]}        p = sortedNil
Sorted'→Sorted {x ∷ []}    p = sorted1
Sorted'→Sorted {x ∷ y ∷ l} p with Sorted'→Sorted {l} {!!}
Sorted'→Sorted {x ∷ y ∷ .[]} p          | sortedNil = {!!}
Sorted'→Sorted {x ∷ y ∷ .(_ ∷ [])} p    | sorted1 = {!!}
Sorted'→Sorted {x ∷ y ∷ .(_ ∷ _ ∷ _)} p | sortedCons z m = {!!}
