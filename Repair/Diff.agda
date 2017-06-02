module Diff where

infix  4 _≡_
infixl 4 _≤_ _≤'_ _≤a_
infixl 6 _+_
infixr 9 _∘_

data _≡_ {ℓ} {A : Set ℓ} (a : A) : A → Set where
  refl : a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}

sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : {A B : Set} → {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong _ refl = refl

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATPLUS _+_ #-}

n≡n+0 : (n : ℕ) → n ≡ n + zero
n≡n+0 zero    = refl
n≡n+0 (suc n) = cong suc (n≡n+0 n)

+-suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm zero n    = n≡n+0 n
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

ℕ-rec : (P : ℕ → Set) → (P zero) → ((n : ℕ) → P n → P (suc n)) → ((n : ℕ) → P n)
ℕ-rec P z s zero    = z
ℕ-rec P z s (suc n) = s n (ℕ-rec P z s n)

plus : ℕ → ℕ → ℕ
plus m n = ℕ-rec (λ _ → ℕ) n (λ _ k → suc k) m

times : ℕ → ℕ → ℕ
times m n = ℕ-rec (λ _ → ℕ) zero (λ _ k → plus k n) m

------------

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

------------

-- Four equivalent characterizations of ≤

-- Coq version
data _≤_ (n : ℕ) : ℕ → Set where
  ln :                   n ≤ n
  ls : {m : ℕ} → n ≤ m → n ≤ suc m

-- indexed version
data _≤'_ : ℕ → ℕ → Set where
  ln : {n : ℕ}            → n ≤' n
  ls : {n m : ℕ} → n ≤' m → n ≤' suc m

-- another version from "A Tutorial on [Co-]Inductive Types in Coq"
data _≤''_ : ℕ → ℕ → Set where
  ln : {n : ℕ}                 → n ≤'' n
  ls : {m n : ℕ} → suc m ≤'' n → m ≤'' n

-- Agda version
data _≤a_ : ℕ → ℕ → Set where
  lz : {n : ℕ}            → zero  ≤a n
  ls : {m n : ℕ} → m ≤a n → suc m ≤a suc n

-----------

n≤sn : {n : ℕ} → n ≤ suc n
n≤sn = ls ln

n≤n+1 : {n : ℕ} → n ≤ n + 1
n≤n+1 {n} rewrite +-comm n 1 = n≤sn

-- go back again
n≤sn' : {n : ℕ} → n ≤ suc n
n≤sn' {n} rewrite +-comm 1 n = n≤n+1

{-
-- fails termination check
mutual
  n≤n+1~m : {n : ℕ} → n ≤ n + 1
  n≤n+1~m {n} rewrite +-comm n 1 = n≤sn~m

  n≤sn~m : {n : ℕ} → n ≤ suc n
  n≤sn~m {n} rewrite +-comm 1 n = n≤n+1~m
-}

≤trans : {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤trans ln     y      = y
≤trans (ls x) ln     = ≤trans x n≤sn
≤trans (ls x) (ls y) = ls (≤trans (ls x) y)

≤transSuc : {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ suc p
≤transSuc x y = ls (≤trans x y)

≤trans+1 : {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p + 1
≤trans+1 {p = p} x y rewrite +-comm p 1 = ls (≤trans x y)

≤'-rec : (P : (m n : ℕ) → m ≤' n → Set)
        → ((n : ℕ) → P n n (ln {n}))
        → ((m n : ℕ) → (x : m ≤' n) → P m n x → P m (suc n) (ls x))
        → ((m n : ℕ) → (x : m ≤' n) → P m n x)
≤'-rec P fn fs m n       ln     = fn m
≤'-rec P fn fs m (suc n) (ls x) = fs m n x (≤'-rec P fn fs m n x)

{-
-- Coq version

Inductive le2 : nat -> nat -> Set :=
| le2_n : forall n, le2 n n
| le2_S : forall n m: nat, le2 n m -> le2 n (S m).


le2_rect = 
fun (P : forall n n0 : nat, le2 n n0 -> Type)
  (f : forall n : nat, P n n (le2_n n))
  (f0 : forall (n m : nat) (l : le2 n m), P n m l -> P n (S m) (le2_S n m l))
=>
fix F (n n0 : nat) (l : le2 n n0) {struct l} : P n n0 l :=
  match l as l0 in (le2 n1 n2) return (P n1 n2 l0) with
  | le2_n n1 => f n1
  | le2_S n1 m l0 => f0 n1 m l0 (F n1 m l0)
  end
     : forall P : forall n n0 : nat, le2 n n0 -> Type,
       (forall n : nat, P n n (le2_n n)) ->
       (forall (n m : nat) (l : le2 n m), P n m l -> P n (S m) (le2_S n m l)) ->
       forall (n n0 : nat) (l : le2 n n0), P n n0 l
-}

-- TODO: Fix this to correspond to Coq.
≤'-ind : (P : {m n : ℕ} → m ≤' n → Set)
        → ({n : ℕ} → P (ln {n}))
        → ({m n : ℕ} → (x : m ≤' n) → P x → P (ls x))
        → ({m n : ℕ} → (x : m ≤' n) → P x)
≤'-ind P n s ln     = n
≤'-ind P n s (ls x) = s x (≤'-ind P n s x)

{-
--- Coq version

Inductive le2 : nat -> nat -> Prop :=
| le2_n : forall n, le2 n n
| le2_S : forall n m: nat, le2 n m -> le2 n (S m).

le2_ind = 
fun (P : nat -> nat -> Prop) (f : forall n : nat, P n n)
  (f0 : forall n m : nat, le2 n m -> P n m -> P n (S m)) =>
fix F (n n0 : nat) (l : le2 n n0) {struct l} : P n n0 :=
  match l in (le2 n1 n2) return (P n1 n2) with
  | le2_n n1 => f n1
  | le2_S n1 m l0 => f0 n1 m l0 (F n1 m l0)
  end
     : forall P : nat -> nat -> Prop,
       (forall n : nat, P n n) ->
       (forall n m : nat, le2 n m -> P n m -> P n (S m)) ->
       forall n n0 : nat, le2 n n0 -> P n n0
-}

----------

n≤asn : {n : ℕ} → n ≤a suc n
n≤asn {zero}  = lz
n≤asn {suc n} = ls (n≤asn {n})

n≤an+1 : {n : ℕ} → n ≤a n + 1
n≤an+1 {zero}  = lz
n≤an+1 {suc n} = ls (n≤an+1 {n})

≤atrans : {m n p : ℕ} → m ≤a n → n ≤a p → m ≤a p
≤atrans lz     _      = lz
≤atrans (ls x) (ls y) = ls (≤atrans x y)

≤atransSuc : {m n p : ℕ} → m ≤a n → n ≤a p → m ≤a  suc p
≤atransSuc lz     y      = lz
≤atransSuc (ls x) (ls y) = ls (≤atransSuc x y)

≤atrans+1 : {m n p : ℕ} → m ≤a n → n ≤a p → m ≤a p + 1
≤atrans+1 lz     y      = lz
≤atrans+1 (ls x) (ls y) = ls (≤atrans+1 x y)

-----------------------

-- Lemmas

≤suc : {m n : ℕ} → m ≤ n → suc m ≤ suc n
≤suc ln     = ln
≤suc (ls x) = ls (≤suc x)

≤asuc : {m n : ℕ} → m ≤a n → m ≤a suc n
≤asuc lz     = lz
≤asuc (ls x) = ls (≤asuc x)

-- Isomorphism between ≤ and ≤'.

≤→≤' : {m n : ℕ} → m ≤ n → m ≤' n
≤→≤' ln     = ln
≤→≤' (ls x) = ls (≤→≤' x)

≤'→≤ : {m n : ℕ} → m ≤' n → m ≤ n
≤'→≤ ln     = ln
≤'→≤ (ls x) = ls (≤'→≤ x)

inverse1 : {m n : ℕ} → (x : m ≤ n) → ≤'→≤ (≤→≤' x) ≡ x
inverse1 ln     = refl
inverse1 (ls x) = cong ls (inverse1 x)

inverse2 : {m n : ℕ} → (x : m ≤' n) → ≤→≤' (≤'→≤ x) ≡ x
inverse2 ln     = refl
inverse2 (ls x) = cong ls (inverse2 x)

-- Isomorphism between ≤ and ≤a.

≤→≤a : {m n : ℕ} → m ≤ n → m ≤a n
≤→≤a {zero}  _      = lz
≤→≤a {suc m} ln     = ls (≤→≤a {m} ln)
≤→≤a {suc m} (ls x) = ≤asuc (≤→≤a {suc m} x)

≤a→≤ : {m n : ℕ} → m ≤a n → m ≤ n
≤a→≤ {zero}  {zero}  _      = ln
≤a→≤ {zero}  {suc n} _      = ls (≤a→≤ lz)
≤a→≤ {suc m} {zero}  ()
≤a→≤ {suc m} {suc n} (ls x) = ≤suc (≤a→≤ {m} {n} x)

{-
inverse1 : {m n : ℕ} → (x : m ≤ n) → ≤a→≤ (≤→≤a x) ≡ x
inverse1 {zero}  {zero}   ln     = refl
inverse1 {zero}  {suc n}  (ls x) = {!!}
inverse1 {suc m} {zero}   ()
inverse1 {suc m} {suc .m} ln     = {!!}
inverse1 {suc m} {suc n}  (ls x) = {!!}

inverse2 : {m n : ℕ} → (x : m ≤a n) → ≤→≤a (≤a→≤ x) ≡ x
inverse2 {zero}  {zero}  lz     = refl
inverse2 {zero}  {suc n} lz     = refl
inverse2 {suc m} {zero}  ()
inverse2 {suc m} {suc n} (ls x) = let z = inverse2 {m} {n} x in {!!}
-}

------------------

-- Several proofs of n≤n+1

-- the original
n≤n+1₀ : {n : ℕ} → n ≤ n + 1
n≤n+1₀ {n} rewrite +-comm n 1 = ls ln

-- using with
n≤n+1₁ : {n : ℕ} → n ≤ n + 1
n≤n+1₁ {n} with n + 1 | +-comm n 1
n≤n+1₁ {n} | .(suc n) | refl = ls ln

-- with desurgaring
n≤n+1₂-aux : {n : ℕ} → (w : ℕ) → w ≡ 1 + n → n ≤ w
n≤n+1₂-aux {n} .(suc n) refl = ls ln

n≤n+1₂ : {n : ℕ} → n ≤ n + 1
n≤n+1₂ {n} = n≤n+1₂-aux {n} (n + 1) (+-comm n 1)

-- convert the proof using Agda ≤
n≤n+1₃ : {n : ℕ} → n ≤ n + 1
n≤n+1₃ = ≤a→≤ n≤an+1

