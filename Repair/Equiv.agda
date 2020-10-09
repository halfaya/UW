{-# OPTIONS --cubical --safe #-}

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
-- You should be able to redefine f (and redo the Iso); everything following should still hold.
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

-- section
fg : (n : ℕ) → f (g n) ≡ n
fg zero                = refl
fg (suc zero)          = refl
fg (suc (suc zero))    = refl
fg (suc (suc (suc n))) = refl

-- retraction
gf : (n : ℕ) → g (f n) ≡ n
gf zero                = refl
gf (suc zero)          = refl
gf (suc (suc zero))    = refl
gf (suc (suc (suc n))) = refl

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

delimA : (P : ℕ → Type) (p0 : P dconA0) (pS : (n : ℕ) → P n → P (dconA1 n)) (n : ℕ) → P n
delimA P p0 pS zero    = p0 
delimA P p0 pS (suc n) = pS n (delimA P p0 pS n)

-- For the second we use the fixed bijection f.

dconB0 : ℕ
dconB0 = f zero

dconB1 : ℕ → ℕ
dconB1 = f ∘ suc ∘ g

-- Utilities and lemmas for delimB

-- Apply function f k times to an argument.
iter : {A : Type} → ℕ → (f : A → A) → A → A
iter zero    f a = a
iter (suc k) f a = f (iter k f a)

-- If we start in A and apply f and then suc k times in the B world,
-- we end up at the same place as applying suc k times in the A world and then f.
-- In other words the obvious rectangle commutes.
sucComm : (k n : ℕ) → iter k dconB1 (f n) ≡ f (iter k dconA1 n)
sucComm zero          n = refl
sucComm (suc zero)    n = cong (f ∘ suc) (gf n)
sucComm (suc (suc k)) n =
  cong dconB1 (sucComm (suc k) n) ∙ 
  subst (λ x → f (suc x) ≡ f (suc (suc (iter k suc n)))) (sym (gf (suc (iter k suc n)))) refl

-- Result of iterating pS k times on p0.
iterS : (P : ℕ → Type) (p0 : P dconB0) (pS : (n : ℕ) → P n → P (dconB1 n)) (n : ℕ) (k : ℕ) → P (iter k dconB1 dconB0)
iterS P p0 pS n zero    = p0
iterS P p0 pS n (suc k) = pS (iter k dconB1 (suc zero)) (iterS P p0 pS n k)

iterSuc : (k : ℕ) → iter k suc zero ≡ k
iterSuc zero    = refl
iterSuc (suc k) = cong suc (iterSuc k)

-- There may be a simpler way to do this, but this is the best I could come up with.
-- Note that the goal is to only depend on f being an Iso, not the details of the implementaton of f.
-- Strategy: Given n, consider k = g n. Iterate pS k times on p0. This results in P n.
delimB : (P : ℕ → Type) (p0 : P dconB0) (pS : (n : ℕ) → P n → P (dconB1 n)) (n : ℕ) → P n
delimB P p0 pS n =
  let k = g n

      a : P (iter k dconB1 dconB0) ≡ P (f (iter k dconA1 (g dconB0)))
      a = cong P (subst (λ x → iter k dconB1 x ≡ f (iter k dconA1 (g dconB0))) (fg dconB0) (sucComm k (g dconB0)))
      
      b : P (iter k dconB1 dconB0) 
      b = iterS P p0 pS n k
      
      c : P (f (iter k dconA1 (g dconB0)))
      c = transport a b
      
      d : f (iter k dconA1 (g dconB0)) ≡ n
      d = subst (λ x → f x ≡ n) (sym (iterSuc k)) (fg n)

  in subst P d c
