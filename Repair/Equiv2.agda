{-# OPTIONS --cubical #-}

module Equiv2 where

open import Cubical.Core.Everything     using (_≡_; Type)
open import Cubical.Foundations.Prelude using (subst)

postulate
  A B : Type
  f   : A → B
  g   : B → A
  fg  : (b : B) → f (g b) ≡ b -- section
  gf  : (a : A) → g (f a) ≡ a -- retraction

-------

dconA : A → A
dconA a = a

delimA : (P : A → Type) (p : (a : A) → P (dconA a)) (a : A) → P a
delimA P p a = p a

-------

dconB : A → B
dconB a = f a

delimB : (P : B → Type) (p : (a : A) → P (dconB a)) (b : B) → P b
delimB P p b = subst P (fg b) (p (g b))

-------

f' : A → B
f' = delimA (λ _ → B) dconB 

g' : B → A
g' = delimB (λ _ → A) dconA

-- section
f'g' : (b : B) → f' (g' b) ≡ b
f'g' b = fg b

-- retraction
g'f' : (a : A) → g' (f' a) ≡ a
g'f' a = gf a
