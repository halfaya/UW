module LeReflect where

open import Data.Nat
open import Data.Nat.Properties
open import Function
open import Relation.Binary.Consequences using (Total)
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

open import Agda.Builtin.Bool
open import Agda.Builtin.Reflection using (Name; Term; TC)
open import Agda.Builtin.Unit

open import IsoReflect

{-
data _≤_ : Rel ℕ Level.zero where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

data _≤′_ (m : ℕ) : ℕ → Set where
  ≤′-refl :                         m ≤′ m
  ≤′-step : ∀ {n} (m≤′n : m ≤′ n) → m ≤′ suc n
-}

-- Conjugation

≤′⇒≤/s≤s : {m n : ℕ} → (x : m ≤′ n) → ≤′⇒≤ (s≤′s x) ≡ s≤s (≤′⇒≤ x)
≤′⇒≤/s≤s ≤′-refl     = refl
≤′⇒≤/s≤s (≤′-step x) = cong ≤-step (≤′⇒≤/s≤s x)

≤⇒≤′/≤-step : {m n : ℕ} → (x : m ≤ n) → ≤⇒≤′ (≤-step x) ≡ ≤′-step (≤⇒≤′ x)
≤⇒≤′/≤-step z≤n     = refl
≤⇒≤′/≤-step (s≤s x) = cong s≤′s (≤⇒≤′/≤-step x)

-- Isomorphism between ≤ and ≤′

≤⇒≤′⇒≤ : {m n : ℕ} → (x : m ≤ n) → ≤′⇒≤ (≤⇒≤′ x) ≡ x
≤⇒≤′⇒≤ {zero}  {zero}  z≤n     = refl
≤⇒≤′⇒≤ {zero}  {suc n} z≤n     = cong ≤-step (≤⇒≤′⇒≤ z≤n)
≤⇒≤′⇒≤                 (s≤s x) rewrite (≤′⇒≤/s≤s (≤⇒≤′ x)) = cong s≤s (≤⇒≤′⇒≤ x)

≤′⇒≤⇒≤′ : {m n : ℕ} → (x : m ≤′ n) → ≤⇒≤′ (≤′⇒≤ x) ≡ x
≤′⇒≤⇒≤′                  (≤′-step x) rewrite (≤⇒≤′/≤-step (≤′⇒≤ x)) = cong ≤′-step (≤′⇒≤⇒≤′ x)
≤′⇒≤⇒≤′ {zero}  {zero}   ≤′-refl     = refl
≤′⇒≤⇒≤′ {suc m} {suc .m} ≤′-refl     = cong s≤′s (≤′⇒≤⇒≤′ {m} {m} ≤′-refl)

-- Trivial Example

0≤1 : 0 ≤ 1
0≤1 = z≤n

0≤′1 : 0 ≤′ 1 -- direct proof
0≤′1 = ≤′-step ≤′-refl

0≤′1′ : 0 ≤′ 1 -- via 0≤1
0≤′1′ = ≤⇒≤′ 0≤1

0≤′1c : 0 ≤′ 1 -- via convert
0≤′1c = convert _≤_ ≤⇒≤′ ≤′⇒≤ 0≤1

-- Note that the proofs are all definitionally equal.

0≤′1≡0≤′1′ : 0≤′1 ≡ 0≤′1′
0≤′1≡0≤′1′ = refl

0≤′1′≡0≤′1c : 0≤′1′ ≡ 0≤′1c
0≤′1′≡0≤′1c = refl

-- Transitivity

≤′-trans : Transitive _≤′_
≤′-trans {i} {j} {k} = λ (a : i ≤′ j) (b : j ≤′ k) → ≤⇒≤′ (≤-trans (≤′⇒≤ a ) (≤′⇒≤ b ))

≤′-transc : Transitive _≤′_ -- via convert
≤′-transc = convert _≤_ ≤⇒≤′ ≤′⇒≤ ≤-trans

≤′-trans≡≤′-transc : {i j k : ℕ} → ≤′-trans {i} {j} {k} ≡ ≤′-transc {i} {j} {k} -- definitionally equal
≤′-trans≡≤′-transc = refl

-- Other properites

-- Note that ≤′-refl is one of the constructors.
≤′-refl′ : Reflexive _≤′_
≤′-refl′ = convert _≤_ ≤⇒≤′ ≤′⇒≤ ≤-refl

-- ≤′-step is also a constructor.
≤′-step′ : ∀ {m n} → m ≤′ n → m ≤′ 1 + n
≤′-step′ = convert _≤_ ≤⇒≤′ ≤′⇒≤ ≤-step

≤′pred⇒≤′ : ∀ {m n} → m ≤′ pred n → m ≤′ n
≤′pred⇒≤′ = convert _≤_ ≤⇒≤′ ≤′⇒≤ ≤pred⇒≤

≤′⇒pred≤′ : ∀ {m n} → m ≤′ n → pred m ≤′ n
≤′⇒pred≤′ = convert _≤_ ≤⇒≤′ ≤′⇒≤ ≤⇒pred≤

-- TODO:

{-
≤′-total : Total _≤′_
≤′-total = convert _≤_ ≤⇒≤′ ≤′⇒≤ ≤-total

n≤′1+n : ∀ n → n ≤′ 1 + n
n≤′1+n = convert _≤_ ≤⇒≤′ ≤′⇒≤ n≤1+n

1+n≰′n : ∀ {n} → ¬ 1 + n ≤′ n
1+n≰′n = convert _≤_ ≤⇒≤′ ≤′⇒≤ 1+n≰n
-}
