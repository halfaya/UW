{-# OPTIONS --without-K --safe --no-import-sorts #-}

module VecFin where

open import Agda.Primitive renaming (Set to Type)

open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

B : (T : Type) → ℕ → Type
B T n = Fin n → T

nil : {T : Type} → B T 0
nil ()

cons : {T : Type} {n : ℕ} → T → B T n → B T (suc n)
cons t b fz     = t
cons _ b (fs f) = b f

hd : {T : Type} {n : ℕ} → B T (suc n) → T
hd b = b fz

tl : {T : Type} {n : ℕ} → B T (suc n) → B T n
tl b f = b (fs f)

-----------

f : {T : Type} (n : ℕ) → Vec T n → B T n
f zero    []       = nil
f (suc n) (x ∷ xs) = cons x (f n xs)

g : {T : Type} (n : ℕ) → B T n → Vec T n
g zero    bn = []
g (suc n) bn = hd bn ∷ g n (tl bn)

gf : {T : Type} (n : ℕ) → (v : Vec T n) → (g n ∘ f n) v ≡ v
gf zero []         = refl
gf (suc n) (x ∷ v) = cong (x ∷_) (gf n v)

fg : {T : Type} (n : ℕ) → (b : B T n) → (m : Fin n) → ((f n ∘ g n) b) m ≡ b m
fg zero    b          ()
fg (suc n) b fz     = refl
fg (suc n) b (fs m) = fg n (tl b) m
