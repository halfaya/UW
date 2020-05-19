{-# OPTIONS --cubical --safe #-}

module NatBin where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude     using (refl; sym; _∙_; cong; transport; subst; funExt; transp; I; i0; i1)
open import Cubical.Foundations.Function    using (_∘_)
open import Cubical.Foundations.Univalence  using (ua)
open import Cubical.Foundations.Isomorphism using (iso; Iso; isoToPath; section; retract)

open import Data.Nat using (ℕ; zero; suc; _>_; s≤s; z≤n; _≤_; _+_)

----------------------
-- Basic data structures

-- unary positive numbers
data Pos : Set where
  one : Pos
  suc : Pos → Pos

-- binary positive numbers
data PosBin : Set where
  pos1 : PosBin           -- 1
  x0   : PosBin → PosBin  -- 2n
  x1   : PosBin → PosBin  -- 2n+1

-- Definition of Bin from the Cubial Agda paper.
-- Note that this differs from the one in BinNat.agda in the current Cubical library.
data Bin : Set where
  bin0   : Bin
  binPos : PosBin → Bin

----------------------

-- Equivalence between ℕ and Pos using suc.

ℕ→Pos : ℕ → Pos
ℕ→Pos zero    = one
ℕ→Pos (suc n) = suc (ℕ→Pos n)

Pos→ℕ : Pos → ℕ
Pos→ℕ one     = zero
Pos→ℕ (suc n) = suc (Pos→ℕ n)

ℕ→Pos→ℕ : (n : ℕ) → Pos→ℕ (ℕ→Pos n) ≡ n
ℕ→Pos→ℕ zero    = refl
ℕ→Pos→ℕ (suc n) = cong suc (ℕ→Pos→ℕ n)

Pos→ℕ→Pos : (n : Pos) → ℕ→Pos (Pos→ℕ n) ≡ n
Pos→ℕ→Pos one     = refl
Pos→ℕ→Pos (suc n) = cong suc (Pos→ℕ→Pos n)

isoℕPos : Iso ℕ Pos
isoℕPos = iso ℕ→Pos Pos→ℕ Pos→ℕ→Pos ℕ→Pos→ℕ

N≡Pos : ℕ ≡ Pos
N≡Pos = isoToPath isoℕPos

-- Equivalence between Pos and the nonzero subset of ℕ.

ℕPos : Set
ℕPos = Σ ℕ (λ n → n > 0)

Pos→ℕPos : Pos → ℕPos
Pos→ℕPos n = suc (Pos→ℕ n) , s≤s (z≤n {Pos→ℕ n})

ℕPos→Pos : ℕPos → Pos
ℕPos→Pos (suc n , _) = ℕ→Pos n

Pos→ℕPos→Pos : (n : Pos) → ℕPos→Pos (Pos→ℕPos n) ≡ n
Pos→ℕPos→Pos = Pos→ℕ→Pos

ℕPos→Pos→ℕPos : (n : ℕPos) → Pos→ℕPos (ℕPos→Pos n) ≡ n
ℕPos→Pos→ℕPos (suc n , s≤s (z≤n {n})) =
  subst (λ x → (suc x , s≤s (z≤n {x})) ≡ (suc n , s≤s (z≤n {n}))) (sym (ℕ→Pos→ℕ n)) refl

isoPosℕPos : Iso Pos ℕPos
isoPosℕPos = iso Pos→ℕPos ℕPos→Pos ℕPos→Pos→ℕPos Pos→ℕPos→Pos

Pos≡ℕPos : Pos ≡ ℕPos
Pos≡ℕPos = isoToPath isoPosℕPos

----------------------

-- Equivalence between Pos and PosBin.
-- This is almost the same equivalence as between ℕ and binnat in BinNat.agda (Cubical library).
-- The constructors have slightly different mathematical meanings.

sucPosBin : PosBin → PosBin
sucPosBin pos1   = x0 pos1
sucPosBin (x0 n) = x1 n
sucPosBin (x1 n) = x0 (sucPosBin n)

doubleℕ : ℕ → ℕ
doubleℕ zero    = zero
doubleℕ (suc n) = suc (suc (doubleℕ n))

-- Might be interesting to lift this from doubleℕ, and see
-- how hard that makes the section/retraction proofs.
doublePos : Pos → Pos
doublePos one     = (suc one)
doublePos (suc n) = suc (suc (doublePos n))

Pos→PosBin : Pos → PosBin
Pos→PosBin one     = pos1
Pos→PosBin (suc n) = sucPosBin (Pos→PosBin n)

PosBin→Pos : PosBin → Pos
PosBin→Pos pos1   = one
PosBin→Pos (x0 n) = doublePos (PosBin→Pos n)
PosBin→Pos (x1 n) = suc (doublePos (PosBin→Pos n))

sucPosBin-suc : (n : PosBin) → PosBin→Pos (sucPosBin n) ≡ suc (PosBin→Pos n)
sucPosBin-suc pos1   = refl
sucPosBin-suc (x0 n) = refl
sucPosBin-suc (x1 n) = cong doublePos (sucPosBin-suc n)

Pos→PosBin→Pos : (n : Pos) → PosBin→Pos (Pos→PosBin n) ≡ n
Pos→PosBin→Pos one     = refl
Pos→PosBin→Pos (suc n) = sucPosBin-suc (Pos→PosBin n) ∙ cong suc (Pos→PosBin→Pos n)

doublePos-x0 : (n : Pos) → Pos→PosBin (doublePos n) ≡ x0 (Pos→PosBin n)
doublePos-x0 one     = refl
doublePos-x0 (suc n) = cong (sucPosBin ∘ sucPosBin) (doublePos-x0 n)

PosBin→Pos→PosBin : (n : PosBin) → Pos→PosBin (PosBin→Pos n) ≡ n
PosBin→Pos→PosBin pos1   = refl
PosBin→Pos→PosBin (x0 n) = doublePos-x0 (PosBin→Pos n) ∙ cong x0 (PosBin→Pos→PosBin n)
PosBin→Pos→PosBin (x1 n) = cong sucPosBin (doublePos-x0 (PosBin→Pos n) ∙ cong x0 (PosBin→Pos→PosBin n))

isoPosPosBin : Iso Pos PosBin
isoPosPosBin = iso Pos→PosBin PosBin→Pos PosBin→Pos→PosBin Pos→PosBin→Pos

Pos≡PosBin : Pos ≡ PosBin
Pos≡PosBin = isoToPath isoPosPosBin
