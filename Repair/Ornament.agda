module Ornament where

open import Data.Nat
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

data Expr : Set where
  const : ℕ → Expr
  add   : Expr → Expr → Expr
  mult  : Expr → Expr → Expr

eval : Expr → ℕ
eval (const n)   = n
eval (add  e e') = eval e + eval e'
eval (mult e e') = eval e * eval e'

data Binop : Set where
  add  : Binop
  mult : Binop

data Expr' : Set where
  const : ℕ → Expr'
  binop : Binop → Expr' → Expr' → Expr'

expr⇒expr' : Expr → Expr'
expr⇒expr' (const n)   = const n
expr⇒expr' (add  e e') = binop add  (expr⇒expr' e) (expr⇒expr' e')
expr⇒expr' (mult e e') = binop mult (expr⇒expr' e) (expr⇒expr' e')

expr'⇒expr : Expr' → Expr
expr'⇒expr (const n)         = const n
expr'⇒expr (binop add  e e') = add  (expr'⇒expr e) (expr'⇒expr e')
expr'⇒expr (binop mult e e') = mult (expr'⇒expr e) (expr'⇒expr e')

eval₁ : Expr' → ℕ
eval₁ (const n)   = n
eval₁ (binop add  e e') = eval₁ e + eval₁ e'
eval₁ (binop mult e e') = eval₁ e * eval₁ e'

eval₂ : Expr' → ℕ
eval₂ = eval ∘ expr'⇒expr

eval₁≡eval₂ : (e : Expr') → eval₁ e ≡ eval₂ e
eval₁≡eval₂ (const n)         = refl
eval₁≡eval₂ (binop add  e e') = cong₂ _+_ (eval₁≡eval₂ e) (eval₁≡eval₂ e')
eval₁≡eval₂ (binop mult e e') = cong₂ _*_ (eval₁≡eval₂ e) (eval₁≡eval₂ e')
