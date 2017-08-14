{-# OPTIONS --without-K #-}

module PatchExamples where

open import Diff

J : {A : Set} → (x : A) → (P : A → Set) → P x → (y : A) → x ≡ y → P y
J P x px y refl = px

-- 1. ≤ variations

-- 2. + variations

infixl 6 _+ᵣ_

_+ᵣ_ : ℕ → ℕ → ℕ
m +ᵣ zero  = m
m +ᵣ suc n = suc (m +ᵣ n)

n≡0+ᵣn : (n : ℕ) → n ≡ 0 +ᵣ n
n≡0+ᵣn zero    = refl
n≡0+ᵣn (suc n) = cong suc (n≡0+ᵣn n)

+ᵣ-suc' : (m n : ℕ) → suc m +ᵣ n ≡ suc (m +ᵣ n)
+ᵣ-suc' m zero    = refl
+ᵣ-suc' m (suc n) = cong suc (+ᵣ-suc' m n)

+≡+ᵣ : (m n : ℕ) → m + n ≡ m +ᵣ n
+≡+ᵣ zero    n = n≡0+ᵣn n
+≡+ᵣ (suc m) n = trans (cong suc (+≡+ᵣ m n)) (sym (+ᵣ-suc' m n))

---

n≡0+ᵣn' : (n : ℕ) → n ≡ 0 +ᵣ n
--n≡0+ᵣn' n = J n (λ x → n ≡ x) refl (0 +ᵣ n) (+≡+ᵣ 0 n)
n≡0+ᵣn' n = +≡+ᵣ 0 n -- simplified

-- note that simplest proof is just refl
n≡n+ᵣ0 : (n : ℕ) → n ≡ n +ᵣ zero
n≡n+ᵣ0 zero    = refl
n≡n+ᵣ0 (suc n) = cong suc (n≡n+ᵣ0 n)

n≡n+ᵣ0' : (n : ℕ) → zero +ᵣ n ≡ n +ᵣ zero
n≡n+ᵣ0' zero    = refl
n≡n+ᵣ0' (suc n) = cong suc (n≡n+ᵣ0' n)

+ᵣ-suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
+ᵣ-suc zero    n = refl
+ᵣ-suc (suc m) n = cong suc (+ᵣ-suc m n)

+ᵣ-comm : (m n : ℕ) → m +ᵣ n ≡ n +ᵣ m
+ᵣ-comm zero n    = n≡n+ᵣ0' n  -- note that n≡n+ᵣ0, even though it has an identical proof to n≡n+ᵣ0', fails!
+ᵣ-comm (suc m) n = {!!} -- trans (cong suc (+ᵣ-comm m n)) (sym (+ᵣ-suc n m))

{-
+-comm' : (m n : ℕ) → m +ᵣ n ≡ n +ᵣ m
+-comm' zero n    = J (n + 0)
                      (λ x → 0 +ᵣ n ≡ x)
                      (J (0 + n)
                         (λ x → x ≡ n + 0)
                         (n≡n+0 (n +ᵣ 0)) -- original proof
                         (0 +ᵣ n)
                         (+≡+ᵣ 0 n))
                      (n +ᵣ 0)
                      (+≡+ᵣ n 0)
+-comm' (suc m) n = {!!} --trans (cong suc (+-comm' m n)) (sym (+-suc n m))
-}


