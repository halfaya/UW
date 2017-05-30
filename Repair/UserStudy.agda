module UserStudy where

open import Data.Bool
open import Data.List
open import Data.List.Properties
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

-- 1

≤transWeak : {n m p : ℕ} → n ≤ m → m ≤ p → n ≤ p + 1
≤transWeak {p = p} a b = ≤-trans (≤-trans a b) (m≤m+n p 1)

≤trans : {n m p : ℕ} → n ≤ m → m ≤ p → n ≤ p
≤trans {p = p} a b = (≤-trans a b)

≤transWeakPatch : ({n m p : ℕ} → n ≤ m → m ≤ p → n ≤ p) →
                  ({n m p : ℕ} → n ≤ m → m ≤ p → n ≤ p + 1)
≤transWeakPatch P {n} {m} {p} b c = ≤-trans (P b c) (m≤m+n p 1)

≤transWeak' : {n m p : ℕ} → n ≤ m → m ≤ p → n ≤ p + 1
≤transWeak' = ≤transWeakPatch ≤trans

-- 2

≤transSuc : {n m p : ℕ} → n ≤ m → m ≤ p → n ≤ suc p
≤transSuc {p = p} a b = ≤-trans (≤-trans a b) (n≤1+n p)

≤transSucPatch : ({n m p : ℕ} → n ≤ m → m ≤ p → n ≤ p) →
                 ({n m p : ℕ} → n ≤ m → m ≤ p → n ≤ suc p)
≤transSucPatch P {n} {m} {p} b c = ≤-trans (P b c) (n≤1+n p)

≤transSuc' : {n m p : ℕ} → n ≤ m → m ≤ p → n ≤ suc p
≤transSuc' = ≤transSucPatch ≤trans

-- 3

<→≤ : {m n : ℕ} → m < n → m ≤ n  -- for reference; not used
<→≤ {n = n@.(suc _)} (s≤s p) = ≤-trans p (n≤1+n (pred n))

<transSuc : {n m p : ℕ} → n ≤ m → m ≤ p → n < suc p
<transSuc {p = p} a b = s≤s (≤-trans a b)

<transSucPatch : ({n m p : ℕ} → n ≤ m → m ≤ p → n ≤ p) →
                 ({n m p : ℕ} → n ≤ m → m ≤ p → n < suc p)
<transSucPatch P {n} {m} {p} b c = s≤s (P b c)

<transSuc' : {n m p : ℕ} → n ≤ m → m ≤ p → n < suc p
<transSuc' = <transSucPatch ≤trans

-- 4

<trans+1 : {n m p : ℕ} → n ≤ m → m ≤ p → n < p + 1
<trans+1 {p = p} a b rewrite +-comm p 1 = s≤s (≤-trans a b)

<trans+1Patch : ({n m p : ℕ} → n ≤ m → m ≤ p → n < suc p) →
                 ({n m p : ℕ} → n ≤ m → m ≤ p → n < p + 1)
<trans+1Patch P {n} {m} {p} b c rewrite +-comm p 1 = P b c

<trans+1' : {n m p : ℕ} → n ≤ m → m ≤ p → n < p + 1
<trans+1' = <trans+1Patch <transSuc

-- 5

data ListSum : List ℕ → ℕ → Set where
  ListSumNil  : ListSum [] 0
  ListSumCons : (h : ℕ) → (tl : List ℕ) → (n : ℕ) → ListSum tl n → ListSum (h ∷ tl) (h + n)

redistSum : (m h m-h n : ℕ) → (h + m-h ≡ m) → (h + (m-h + n) ≡ m + n)
redistSum m       zero    m-h n a rewrite a = refl
redistSum zero    (suc h) m-h n ()
redistSum (suc m) (suc h) m-h n a rewrite redistSum m h m-h n (cong pred a) = refl

listSumRevRev≡ : {n : ℕ} → {l : List ℕ}  → ListSum l n → ListSum (reverse (reverse l)) n
listSumRevRev≡ {l = l} ls rewrite reverse-involutive l = ls

listSum : {m n : ℕ} → {l₁ l₂ : List ℕ} → ListSum l₁ m → ListSum (l₁ ++ l₂) (m + n) → ListSum l₂ n
listSum ListSumNil b = b
listSum (ListSumCons h tl m-h a) b = {!let x = listSum a b in ?!}

listSumRevRev : {m n : ℕ} → {l₁ l₂ : List ℕ} → ListSum l₁ m → ListSum (l₁ ++ l₂) (m + n) → ListSum (reverse (reverse l₂)) n
listSumRevRev a b = listSumRevRev≡ (listSum a b)

listSumRevRevPatch : ({m n : ℕ} → {l₁ l₂ : List ℕ} → ListSum l₁ m → ListSum (l₁ ++ l₂) (m + n) → ListSum l₂ n) →
                     ({m n : ℕ} → {l₁ l₂ : List ℕ} → ListSum l₁ m → ListSum (l₁ ++ l₂) (m + n) → ListSum (reverse (reverse l₂)) n)
                     
listSumRevRevPatch P a b = listSumRevRev≡ (P a b)

listSumRevRev' : {m n : ℕ} → {l₁ l₂ : List ℕ} → ListSum l₁ m → ListSum (l₁ ++ l₂) (m + n) → ListSum (reverse (reverse l₂)) n
listSumRevRev' = listSumRevRevPatch listSum
                     
-- 6

reverse-preserves-length : {A : Set} → (l : List A) → length l ≡ length (reverse l)
reverse-preserves-length []      = refl
reverse-preserves-length (x ∷ l) = let y = reverse-preserves-length l in {!!}

++length : {A : Set} → (l₁ l₂ : List A) → length (l₁ ++ l₂) ≡ length l₁ + length l₂
++length []      m = refl
++length (x ∷ l) m = cong suc (++length l m)

-- 7

×→⊎ : {A B : Set} → A × B → A ⊎ B
×→⊎ (A , _) = inj₁ A

∧or-type : Set
∧or-type = (a b : Bool) → a ∧ b ≡ true → a ≡ true ⊎ b ≡ true

∧or : ∧or-type
∧or false _ ()
∧or true  _ _ = inj₁ refl

∧and-type : Set
∧and-type = (a b : Bool) → a ∧ b ≡ true → a ≡ true × b ≡ true

∧and : ∧and-type
∧and false b     ()
∧and true  false ()
∧and true  true  _ = refl , refl

∧or-patch : ∧and-type → ∧or-type
∧or-patch P a b p = ×→⊎ (P a b p)

∧or' : ∧or-type
∧or' = ∧or-patch ∧and

-- 8

data _∈_ {A : Set} (a : A) : (l : List A) → Set where
  here  : {as : List A} → a ∈ (a ∷ as)
  there : {b : A} → {as : List A} → a ∈ as → a ∈ (b ∷ as)

reverse-preserves-∈ : {A : Set} → {a : A} → {l : List A} → a ∈ l → a ∈ reverse l
reverse-preserves-∈ {A} {a} {.(a ∷ _)} here      = {!!}
reverse-preserves-∈ {A} {a} {.(_ ∷ _)} (there p) = {!!}

in-map : {A B : Set} → {f : A → B} → {a : A} → {l : List A} → a ∈ l → f a ∈ Data.List.map f l
in-map here      = here
in-map (there p) = there (in-map p)

in-map-rev : {A B : Set} → {f : A → B} → {a : A} → {l : List A} → a ∈ l → f a ∈ reverse (Data.List.map f l)
in-map-rev = reverse-preserves-∈ ∘ in-map

in-map-rev-patch : ({A B : Set} → {f : A → B} → {a : A} → {l : List A} → a ∈ l → f a ∈ Data.List.map f l) →
                    {A B : Set} → {f : A → B} → {a : A} → {l : List A} → a ∈ l → f a ∈ reverse (Data.List.map f l)
in-map-rev-patch P p = reverse-preserves-∈ (P p) 

in-map-rev' : {A B : Set} → {f : A → B} → {a : A} → {l : List A} → a ∈ l → f a ∈ reverse (Data.List.map f l)
in-map-rev' = in-map-rev-patch in-map

-- misc

<A'→A>→<B→C>→<<A→B>→<B→C>> : {A A' B C : Set} → (A' → A) → (B → C) → ((A → B) → (A' → C))
<A'→A>→<B→C>→<<A→B>→<B→C>> f g h = g ∘ h ∘ f

thm : (a b : ℕ) → (P : ℕ → Set) → P (a + b) → P (b + a)
thm a b P Px with (a + b) | +-comm a b
thm a b P Px | .(b + a) | refl = Px

inR : {A : Set} → {a : A} → {l r : List A} → a ∈ r → a ∈ (l ++ r)
inR {l = []}    p = p
inR {l = x ∷ l} p = there (inR {l = l} p)

inTheList : {x y z : ℕ} → x ∈ ((y ∷ []) ++ (z ∷ x ∷ []))
inTheList {y = y} = inR {l = y ∷ []} (there here)

data Vec (A : Set): ℕ → Set where
  []  : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

v : Vec _ _
v = zero ∷ []

n = zero
