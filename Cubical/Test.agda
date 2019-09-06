{-# OPTIONS --cubical --safe #-}

module Test where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Agda.Builtin.List
open import Data.Vec

-- Strangely even though Σ-eq₂ is defined in the paper, I can't find
-- either of these in the Cubical library, so I'm defining them here.
Σ-eq₁ : {a b : Level} {A : Set a} {B : A → Set b} {p q : Σ A B} → (p ≡ q) →
  fst p ≡ fst q
Σ-eq₁ = cong fst

Σ-eq₂ : {a b : Level} {A : Set a} {B : A → Set b} {p q : Σ A B} → (e : p ≡ q) →
  PathP (λ i → B (fst (e i))) (snd p) (snd q)
Σ-eq₂ = cong snd

-- Generalization of cong to paths. Might be in the Cubical library somewhere.
congPath : {a b : Level} {A : I → Set a} {B : (r : I) → A r → Set b}
  (f : {r : I} → (a : A r) → B r a) → {x : A i0} → {y : A i1} → 
  (p : PathP A x y) → PathP (λ i → B i (p i)) (f {i0} x) (f {i1} y)
congPath f p i = f {i} (p i)

module _ {ℓ} {A : Type ℓ} where

  List→Vec : List A → Σ ℕ (Vec A)
  List→Vec []       = 0 , []
  List→Vec (x ∷ xs) = let (n , ys) = List→Vec xs in (suc n , x ∷ ys)

  Vec→List : Σ ℕ (Vec A) → List A
  Vec→List (zero  , [])     = []
  Vec→List (suc n , x ∷ xs) = x ∷ Vec→List (n , xs)

  List→Vec→List : (xs : List A) → Vec→List (List→Vec xs) ≡ xs
  List→Vec→List []       = refl
  List→Vec→List (x ∷ xs) = let a = List→Vec→List xs in {!!}

  Vec→List→Vec : (v : Σ ℕ (Vec A)) → List→Vec (Vec→List v) ≡ v
  Vec→List→Vec (zero , [])      = refl
  Vec→List→Vec (suc n , x ∷ xs) =
    let a : List→Vec (Vec→List (n , xs)) ≡ (n , xs)                                     ; a = Vec→List→Vec (n , xs)
        b : suc (fst (List→Vec (Vec→List (n , xs)))) ≡ suc n                            ; b = cong suc (Σ-eq₁ a)
        c : PathP (λ i → Vec A (b i)) (x ∷ snd (List→Vec (Vec→List (n , xs)))) (x ∷ xs) ; c = congPath (x ∷_) (Σ-eq₂ a)
    in ΣPathP (b , c)

  List≃Vec : List A ≃ Σ ℕ (Vec A)
  List≃Vec = isoToEquiv (iso List→Vec Vec→List Vec→List→Vec List→Vec→List)

  List≡Vec : List A ≡ Σ ℕ (Vec A)
  List≡Vec = ua List≃Vec
