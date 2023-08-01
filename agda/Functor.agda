{-# OPTIONS --cubical --safe #-}

module Functor where

open import Cubical.Core.Everything using (Level; Type; _≡_)
open import Cubical.Foundations.Prelude using (refl; cong; funExt)
open import Data.List using (List; []; _∷_) renaming (map to mapList)

infix 4 _🟰_
_🟰_ : {ℓ : Level} {A : Type ℓ} → A → A → Type ℓ
_🟰_ = _≡_

id : {ℓ : Level} (A : Type ℓ) → A → A
id A = λ x → x

_∘_ : {A B C : Type} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

record Functor : Type₁ where
  field
    F   : Type → Type                          -- F₀
    map : {A B : Type} → (A → B) → (F A → F B) -- F₁

    mapId   : {A : Type} →
              map (id A) 🟰 id (F A)
    mapComp : {A B C : Type} → {f : A → B} → {g : B → C} →
              map (g ∘ f) 🟰 map g ∘ map f

idFunctor : Functor
idFunctor = record {
  F       = id Type;
  map     = λ {A B} → id (A → B);
  mapId   = refl;
  mapComp = refl}

mapListId : {A : Type} → (x : List A) → mapList (id A) x 🟰 id (List A) x
mapListId []       = refl
mapListId (x ∷ xs) = cong (x ∷_) (mapListId xs)

mapListComp : {A B C : Type} {f : A → B} {g : B → C} → (x : List A) →
              mapList (g ∘ f) x 🟰 (mapList g ∘ mapList f) x
mapListComp []                      = refl
mapListComp {f = f}{g = g} (x ∷ xs) = cong (g (f x) ∷_) (mapListComp xs)

listFunctor : Functor
listFunctor = record {
  F       = List;
  map     = mapList;
  mapId   = funExt mapListId;
  mapComp = funExt mapListComp }
