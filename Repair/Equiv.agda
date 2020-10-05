{-# OPTIONS --cubical #-} -- Not safe since there is a function not known to be terminating.

module Equiv where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude     using (refl; sym; _∙_; cong; transport; subst; funExt; transp; I; i0; i1; hcomp; primPOr; _∨_)
open import Cubical.Foundations.Function    using (_∘_)
open import Cubical.Foundations.Isomorphism using (iso; Iso; isoToPath; section; retract; isoToEquiv)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- Consider a fixed self-equivalence of ℕ.
-- Start with a simple one that rotates 0, 1 and 2 (we want to avoid involutions).
f : ℕ → ℕ
f zero                = suc zero
f (suc zero)          = suc (suc zero)
f (suc (suc zero))    = zero
f (suc (suc (suc n))) = suc (suc (suc n))

-- The inverse function (call it g) rotates the other direction.
g : ℕ → ℕ
g zero                = suc (suc zero)
g (suc zero)          = zero
g (suc (suc zero))    = suc zero
g (suc (suc (suc n))) = suc (suc (suc n))

-- Section and retraction are definitional in this simple case, but won't be in general.

gf : (n : ℕ) → g (f n) ≡ n
gf zero                = refl
gf (suc zero)          = refl
gf (suc (suc zero))    = refl
gf (suc (suc (suc n))) = refl

fg : (n : ℕ) → f (g n) ≡ n
fg zero                = refl
fg (suc zero)          = refl
fg (suc (suc zero))    = refl
fg (suc (suc (suc n))) = refl

fIso : Iso ℕ ℕ
fIso = iso f g fg gf

fEq : ℕ ≡ ℕ
fEq = isoToPath fIso

-- We now create dep_constr (dcon) and dep_elim (delim) for each ℕ.
-- For the first we use the standard constructors and eliminator for ℕ.

dconA0 : ℕ
dconA0 = zero

dconA1 : ℕ → ℕ
dconA1 = suc

delimA : {A : Set} (P : ℕ → Set) (p0 : P zero) (pS : (n : ℕ) → P n → P (suc n)) (n : ℕ) → P n
delimA     P p0 pS zero    = p0 
delimA {A} P p0 pS (suc n) = pS n (delimA {A} P p0 pS n)  -- For some reason Agda needs A in this case.

-- For the second we use the fixed bijection f.

dconB0 : ℕ
dconB0 = f zero

dconB1 : ℕ → ℕ
dconB1 = f ∘ suc

{-# TERMINATING #-}
delimB : {A : Set} (P : ℕ → Set) (p0 : P (f zero)) (pS : (n : ℕ) → P n → P (f (suc n))) (n : ℕ) → P (f n)
delimB     P p0 pS zero    = p0 
delimB {A} P p0 pS (suc n) = pS n (subst P (fg n) (delimB {A} P p0 pS (g n)))


