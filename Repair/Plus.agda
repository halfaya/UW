module Plus where

infix  4 _≡_
infixl 6 _+_ _⊕_ _⊞_

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

-- induction on the second argument
_⊕_ : ℕ → ℕ → ℕ
m ⊕ zero = m
m ⊕ suc n = suc (m ⊕ n)

n≡n+0 : (n : ℕ) → n ≡ n + zero
n≡n+0 zero    = refl
n≡n+0 (suc n) = cong suc (n≡n+0 n)

n≡0⊕n : (n : ℕ) → n ≡ zero ⊕ n
n≡0⊕n zero    = refl
n≡0⊕n (suc n) = cong suc (n≡0⊕n n)

+-suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

⊕-suc : (m n : ℕ) → suc m ⊕ n ≡ suc (m ⊕ n)
⊕-suc m zero    = refl
⊕-suc m (suc n) = cong suc (⊕-suc m n)

+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm zero n    = n≡n+0 n
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

-- the two are equivalent

+→⊕ : (m n : ℕ) → m + n ≡ m ⊕ n
+→⊕ zero    n = n≡0⊕n n
+→⊕ (suc m) n = trans (cong suc (+→⊕ m n)) (sym (⊕-suc m n))

⊕→+ : (m n : ℕ) → m ⊕ n ≡ m + n
⊕→+ m zero    = n≡n+0 m
⊕→+ m (suc n) = trans (cong suc (⊕→+ m n)) (sym (+-suc m n))

-- try induction on the other variable
+→⊕' : (m n : ℕ) → m + n ≡ m ⊕ n
+→⊕' m zero    = sym (n≡n+0 m)
+→⊕' m (suc n) = trans (+-suc m n) (cong suc (+→⊕' m n))

---

ℕ-rec : (P : ℕ → Set) → (P zero) → ((n : ℕ) → P n → P (suc n)) → ((n : ℕ) → P n)
ℕ-rec P z s zero    = z
ℕ-rec P z s (suc n) = s n (ℕ-rec P z s n)

_⊞_ : ℕ → ℕ → ℕ
_⊞_ = λ m n → ℕ-rec (λ _ → ℕ) n (λ _ k → suc k) m

_⊞'_ : ℕ → ℕ → ℕ
_⊞'_ = λ n m → ℕ-rec (λ _ → ℕ) n (λ _ k → suc k) m

times : ℕ → ℕ → ℕ
times m n = ℕ-rec (λ _ → ℕ) zero (λ _ k → k ⊞ n) m

n≡0⊞n : (n : ℕ) → n ≡ zero ⊞ n
n≡0⊞n n = refl

n≡n⊞0 : (n : ℕ) → n ≡ n ⊞ zero
n≡n⊞0 zero    = refl
n≡n⊞0 (suc n) = cong suc (n≡n⊞0 n)

⊞→+ : (m n : ℕ) → m ⊞ n ≡ m + n
⊞→+ zero n    = refl
⊞→+ (suc m) n = let x = ⊞→+ m n in {!!}  

⊞-comm : (m n : ℕ) → m ⊞ n ≡ n ⊞ m
⊞-comm zero    n = {!!}
⊞-comm (suc m) n = {!!}
