{-# OPTIONS --cubical --safe #-}

module Pitch where

open import Cubical.Core.Everything using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)

open import Cubical.Foundations.Prelude     using (refl; sym; _∙_; cong; transport; subst; funExt; transp; I; i0; i1)
open import Cubical.Foundations.Function    using (_∘_)
open import Cubical.Foundations.Univalence  using (ua)
open import Cubical.Foundations.Isomorphism using (iso; Iso; isoToPath; section; retract; isoToEquiv)

open import Data.List       using (List; length; []; _∷_)
open import Data.Fin        using (Fin; toℕ; #_; _≟_) renaming (zero to fz; suc to fs)
open import Data.Nat        using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.DivMod using (_mod_; _div_)
open import Data.Product    using (_×_; _,_; proj₁)
open import Data.Unit       using (⊤; tt)
open import Data.Vec        using (Vec; []; _∷_)

-- Position of a pitch on an absolute scale
-- 0 is C(-1) on the international scale (where C4 is middle C)
-- or C0 on the Midi scale (where C5 is middle C)
-- Pitch is intentially set to match Midi pitch.
-- However it is fine to let 0 represent some other note and
-- translate appropriately at the end.
data Pitch : Set where
  pitch : ℕ → Pitch

-- Number of notes in the chromatic scale.
chromaticScaleSize : ℕ
chromaticScaleSize = 12

-- Position of a pitch within an octave, in the range [0..chromaticScaleSize-1].
data PitchClass : Set where
  pitchClass : Fin chromaticScaleSize → PitchClass

-- Which octave one is in.
data Octave : Set where
  octave : ℕ → Octave

PitchOctave : Set
PitchOctave = PitchClass × Octave

rel→abs : PitchOctave → Pitch
rel→abs (pitchClass n , octave o) =
  pitch (o * chromaticScaleSize + (toℕ n))

abs→rel : Pitch → PitchOctave
abs→rel (pitch  n) =
  (pitchClass (n mod chromaticScaleSize) , octave (n div chromaticScaleSize))

rel→abs→rel : (p : PitchOctave) → (abs→rel ∘ rel→abs) p ≡ p
rel→abs→rel (pitchClass p , octave o) = {!!}

abs→rel→abs : (p : Pitch) → (rel→abs ∘ abs→rel) p ≡ p
abs→rel→abs (pitch p) =
  let a = {!!}
  in cong pitch {!!}

-- p / 12 * 12 + p % 12 = p

abs≃rel : Iso Pitch PitchOctave
abs≃rel = iso abs→rel rel→abs rel→abs→rel abs→rel→abs

abs≡rel : Pitch ≡ PitchOctave
abs≡rel = isoToPath abs≃rel
