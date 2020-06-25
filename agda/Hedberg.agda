{-# OPTIONS --without-K --safe #-}

-- Proof of Hedberg's Theorem
-- Adapted from http://www.cse.chalmers.se/~nad/listings/equality/Equality.Decidable-UIP.html

module Hedberg where

open import Agda.Primitive                        using (Level; _⊔_)
open import Data.Empty                            using (⊥; ⊥-elim)
open import Data.Product                          using (Σ; _,_; proj₁; proj₂)
open import Function                              using (id; const; _∘_)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary                      using (Dec; yes; no)

-- Definitions.

infixr 5 _∙_
_∙_ = trans

Is-proposition : {ℓ : Level} → Set ℓ → Set ℓ
Is-proposition A = (x y : A) → x ≡ y

Is-set : {ℓ : Level} → Set ℓ → Set ℓ
Is-set A = (x y : A) → Is-proposition (x ≡ y)

Constant : {ℓ ℓ′ : Level} {A : Set ℓ} {B : Set ℓ′} → (A → B) → Set (ℓ ⊔ ℓ′)
Constant {A = A} f = (x y : A) → f x ≡ f y

Decidable-equality : {ℓ : Level} → Set ℓ → Set ℓ
Decidable-equality A = Decidable (_≡_ {A = A})

_Left-inverse-of_ : {ℓ ℓ′ : Level} {A : Set ℓ} {B : Set ℓ′} → (B → A) → (A → B) → Set ℓ
_Left-inverse-of_ {A = A} g f = (x : A) → g (f x) ≡ x

-- Construction of a left inverse in the path space of _≡_
left-inverse : {ℓ : Level} {A : Set ℓ} →
               (f : (x y : A) → x ≡ y → x ≡ y) → (x y : A) → (x ≡ y → x ≡ y)
left-inverse f x y = λ x≡y → x≡y ∙ sym (f y y refl)

------------------------------------------------------

-- refl is the identity of the path space of _≡_
refl-groupoid-id : {ℓ : Level} {A : Set ℓ} → (x y : A) → (e : x ≡ y) →
                   e ∙ sym e ≡ refl
refl-groupoid-id x .x refl = refl

-- A type with a constant endofunction with a left inverse is a proposition.
left-inverse⇒proposition : {ℓ : Level} {A : Set ℓ} → (f g : A → A) →
                         Constant f → g Left-inverse-of f → Is-proposition A
left-inverse⇒proposition f g constant li x y =
  let a : x       ≡ g (f x) ; a = sym (li x)
      b : g (f x) ≡ g (f y) ; b = cong g (constant x y)
      c : g (f y) ≡ y       ; c = li y
  in a ∙ b ∙ c

-- Endofunction families on _≡_ always have left inverses.
≡-has-left-inverse : {ℓ : Level} {A : Set ℓ} → (f : (x y : A) → x ≡ y → x ≡ y) → 
             (x y : A) → (left-inverse f x y) Left-inverse-of (f x y)
≡-has-left-inverse {A = A} f x .x refl = refl-groupoid-id x x (f x x refl)

-- A type A is a set if there is a family of constant endofunctions on _≡_ {A = A}.
constant⇒set : {ℓ : Level} {A : Set ℓ} → 
               ((x y : A) → Σ (x ≡ y → x ≡ y) (λ f → Constant f)) → Is-set A
constant⇒set fconst x y =
  let (f , constant) = fconst x y
      ff             = λ x y → proj₁ (fconst x y)
  in left-inverse⇒proposition f (left-inverse ff x y) constant (≡-has-left-inverse ff x y)

-- Types which are decidable come with constant endofunctions.
decidable⇒constant : {ℓ : Level} {A : Set ℓ} → Dec A → Σ (A → A) (λ f → Constant f)
decidable⇒constant (yes x) = const x , λ _ _ → refl
decidable⇒constant (no ¬x) = id      , λ _   → ⊥-elim ∘ ¬x

-- Hedberg's Thoerem:  Types with decidable equality are sets.
decidable⇒set : {ℓ : Level} {A : Set ℓ} → Decidable-equality A → Is-set A
decidable⇒set dec = constant⇒set (λ x y → decidable⇒constant (dec x y))
